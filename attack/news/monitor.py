#!/usr/bin/env python3
"""GOLDBACH ATTACK news monitor.

Poll the arXiv Atom API for Goldbach-related papers, deduplicate by arXiv id,
score relevance, and append new entries to news/feed.jsonl. State (last run,
seen ids, feed checksum) lives in news/state.json.

Stdlib only. Commands:

    python3 news/monitor.py once
    python3 news/monitor.py watch --interval 1800
    python3 news/monitor.py digest
"""

import argparse
import datetime
import hashlib
import json
import pathlib
import re
import sys
import time
import urllib.error
import urllib.request
import xml.etree.ElementTree as ET

# --- configuration -----------------------------------------------------------

QUERIES = [
    # Broad subject search, newest first.
    "http://export.arxiv.org/api/query?search_query=all:Goldbach"
    "&start=0&max_results=100&sortBy=submittedDate&sortOrder=descending",
    # Focused title search, catches papers whose abstract omits the word.
    "http://export.arxiv.org/api/query?search_query=ti:Goldbach"
    "&start=0&max_results=100&sortBy=submittedDate&sortOrder=descending",
]

USER_AGENT = (
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/124.0 Safari/537.36 GOLDBACH-ATTACK-news-monitor/1.0"
)
TIMEOUT_SECONDS = 20
REQUESTS_PER_QUERY = 2  # one attempt + one retry -> at most 4 requests per run
MAX_ENTRIES_DIGEST = 20
MAX_ENTRIES_ONCE = 10

KEYWORDS = [
    "goldbach",
    "chen",
    "sieve",
    "prime",
    "exceptional set",
    "grh",
    "liu",
    "fundamental lemma",
    "circle method",
    "additive",
]
KEYWORD_PATTERNS = [
    (term, re.compile(r"\b" + re.escape(term) + r"(?:s|'s)?\b", re.IGNORECASE))
    for term in KEYWORDS
]

ATOM = {"a": "http://www.w3.org/2005/Atom"}
HERE = pathlib.Path(__file__).resolve().parent
FEED_PATH = HERE / "feed.jsonl"
STATE_PATH = HERE / "state.json"


def now_utc():
    """Return an ISO-8601 UTC timestamp with a Z suffix."""
    return (
        datetime.datetime.now(datetime.timezone.utc)
        .isoformat(timespec="seconds")
        .replace("+00:00", "Z")
    )


def warn(message):
    print("warning: " + message, file=sys.stderr)


# --- scoring -----------------------------------------------------------------


def score_text(text):
    """Return (score, matched_keywords) for a piece of text."""
    score = 0
    matched = []
    for term, pattern in KEYWORD_PATTERNS:
        count = len(pattern.findall(text))
        if count:
            score += count
            matched.append(term)
    return score, matched


# --- network -----------------------------------------------------------------


class Fetcher:
    """Fetch Atom feeds with a hard cap on HTTP requests per run."""

    def __init__(self, max_requests=len(QUERIES) * REQUESTS_PER_QUERY):
        self.max_requests = max_requests
        self.used = 0

    def _get(self, url):
        if self.used >= self.max_requests:
            warn("HTTP request budget exhausted (%d requests)" % self.max_requests)
            return None
        self.used += 1
        request = urllib.request.Request(
            url,
            headers={
                "User-Agent": USER_AGENT,
                "Accept": "application/atom+xml, application/xml;q=0.9, */*;q=0.8",
            },
        )
        try:
            with urllib.request.urlopen(request, timeout=TIMEOUT_SECONDS) as response:
                return response.read()
        except (urllib.error.URLError, OSError, TimeoutError) as exc:
            warn("request %d/%d failed for %s: %s" % (self.used, self.max_requests, url, exc))
            return None

    def fetch(self, url):
        """Fetch with one retry; return bytes or None on failure."""
        for attempt in range(REQUESTS_PER_QUERY):
            data = self._get(url)
            if data is not None:
                if attempt:
                    print("  retry succeeded for %s" % url)
                return data
            if attempt + 1 < REQUESTS_PER_QUERY:
                print("  retrying %s" % url)
        warn("giving up on %s" % url)
        return None


# --- parsing -----------------------------------------------------------------


def clean(text):
    return " ".join((text or "").split())


def arxiv_id(raw):
    """Normalise an Atom id like http://arxiv.org/abs/2401.12345v2 to 2401.12345."""
    value = clean(raw)
    match = re.search(r"/abs/([^/?#]+)", value)
    if match:
        value = match.group(1)
    elif value.startswith(("http://", "https://")):
        value = value.rstrip("/").split("/")[-1]
    return re.sub(r"v\d+$", "", value)


def parse_atom(data):
    """Parse an Atom feed into a list of entry dicts. Raise on bad XML."""
    root = ET.fromstring(data)
    entries = []
    for element in root.findall("a:entry", ATOM):
        rid = arxiv_id(element.findtext("a:id", default="", namespaces=ATOM))
        if not rid:
            continue
        title = clean(element.findtext("a:title", default="", namespaces=ATOM))
        abstract = clean(element.findtext("a:summary", default="", namespaces=ATOM))
        authors = [
            clean(name.text)
            for name in element.findall("a:author/a:name", ATOM)
            if name.text and clean(name.text)
        ]
        score, keywords = score_text(title + " " + abstract)
        entries.append(
            {
                "id": rid,
                "title": title,
                "authors": authors,
                "abstract": abstract[:500],
                "published": clean(
                    element.findtext("a:published", default="", namespaces=ATOM)
                ),
                "updated": clean(element.findtext("a:updated", default="", namespaces=ATOM)),
                "url": "https://arxiv.org/abs/" + rid,
                "found_at": now_utc(),
                "keywords": keywords,
                "score": score,
            }
        )
    return entries


# --- storage -----------------------------------------------------------------


def read_feed():
    entries = []
    if not FEED_PATH.exists():
        return entries
    with FEED_PATH.open("r", encoding="utf-8") as handle:
        for number, line in enumerate(handle, 1):
            line = line.strip()
            if not line:
                continue
            try:
                item = json.loads(line)
            except json.JSONDecodeError as exc:
                warn("skipping malformed %s line %d: %s" % (FEED_PATH.name, number, exc))
                continue
            if isinstance(item, dict) and item.get("id"):
                entries.append(item)
    return entries


def read_state():
    default = {"last_run": None, "last_seen_ids": [], "last_new_ids": []}
    if not STATE_PATH.exists():
        return default
    try:
        with STATE_PATH.open("r", encoding="utf-8") as handle:
            saved = json.load(handle)
    except (OSError, json.JSONDecodeError) as exc:
        warn("could not read %s: %s (starting fresh)" % (STATE_PATH.name, exc))
        return default
    if not isinstance(saved, dict):
        return default
    for key, fallback in default.items():
        saved.setdefault(key, fallback)
    return saved


def write_json(path, payload):
    with path.open("w", encoding="utf-8") as handle:
        json.dump(payload, handle, ensure_ascii=False, indent=2, sort_keys=True)
        handle.write("\n")


def append_entries(entries):
    with FEED_PATH.open("a", encoding="utf-8") as handle:
        for entry in entries:
            handle.write(json.dumps(entry, ensure_ascii=False, sort_keys=True) + "\n")


# --- commands ----------------------------------------------------------------


def poll():
    """Run one poll: fetch, dedupe, append, update state. Return new entries."""
    fetcher = Fetcher()
    collected = {}
    successes = 0
    for url in QUERIES:
        data = fetcher.fetch(url)
        if data is None:
            continue
        try:
            parsed = parse_atom(data)
        except ET.ParseError as exc:
            warn("bad Atom XML from %s: %s" % (url, exc))
            continue
        successes += 1
        for entry in parsed:
            collected.setdefault(entry["id"], entry)
        print("fetched %d entries from %s" % (len(parsed), url.split("?")[0]))

    if not successes:
        warn("all arXiv queries failed; keeping existing feed and state")
        return []

    old_feed = read_feed()
    state = read_state()
    seen = {entry["id"] for entry in old_feed}
    seen.update(state.get("last_seen_ids") or [])
    new = [entry for rid, entry in collected.items() if rid not in seen]
    # Highest relevance first; newest publication breaks ties.
    new.sort(key=lambda e: (e["score"], e["published"]), reverse=True)

    if new:
        append_entries(new)
    write_json(
        STATE_PATH,
        {
            "last_run": now_utc(),
            "last_seen_ids": sorted(seen | set(collected)),
            "last_new_ids": [entry["id"] for entry in new],
            "total_entries": len(old_feed) + len(new),
            "feed_sha256": hashlib.sha256(FEED_PATH.read_bytes()).hexdigest()
            if FEED_PATH.exists()
            else None,
        },
    )
    print(
        "poll complete: %d/%d queries OK, %d parsed, %d new (feed: %d entries)"
        % (successes, len(QUERIES), len(collected), len(new), len(old_feed) + len(new))
    )
    return new


def print_new(new):
    if not new:
        print("No new Goldbach papers.")
        return
    print("NEW entries (%d):" % len(new))
    for index, entry in enumerate(new[:MAX_ENTRIES_ONCE], 1):
        print(
            "  %2d. [score %2d] %s (%s) %s"
            % (
                index,
                entry["score"],
                entry["title"],
                entry["id"],
                entry["published"][:10],
            )
        )
        if entry["keywords"]:
            print("       keywords: " + ", ".join(entry["keywords"]))
        print("       " + entry["url"])
    if len(new) > MAX_ENTRIES_ONCE:
        print("  ... and %d more (see %s)" % (len(new) - MAX_ENTRIES_ONCE, FEED_PATH.name))


def print_digest(limit=MAX_ENTRIES_DIGEST):
    entries = read_feed()[-limit:]
    if not entries:
        print("Feed is empty. Run `python3 news/monitor.py once` first.")
        return
    print("Last %d entries in %s (oldest of the batch first):" % (len(entries), FEED_PATH))
    for index, entry in enumerate(entries, 1):
        print("-" * 72)
        print("%d. [score %2d] %s" % (index, entry.get("score", 0), entry.get("title", "")))
        print("   id:        %s" % entry.get("id", ""))
        print("   authors:   %s" % (", ".join(entry.get("authors") or []) or "unknown"))
        print("   published: %s   updated: %s" % (entry.get("published", ""), entry.get("updated", "")))
        print("   found_at:  %s" % entry.get("found_at", ""))
        print("   keywords:  %s" % (", ".join(entry.get("keywords") or []) or "none"))
        print("   url:       %s" % entry.get("url", ""))
        print("   abstract:  %s" % (entry.get("abstract", "")[:300]))
    print("-" * 72)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("once", help="poll once and print a digest of new entries")
    watch = sub.add_parser("watch", help="poll repeatedly (Ctrl-C to stop)")
    watch.add_argument(
        "--interval", type=int, default=1800, help="seconds between polls (default: 1800)"
    )
    sub.add_parser("digest", help="print the last 20 feed entries")
    args = parser.parse_args(argv)

    if args.command == "digest":
        print_digest()
        return 0
    if args.command == "once":
        print_new(poll())
        return 0
    if args.interval <= 0:
        parser.error("--interval must be positive")
    while True:
        try:
            print("\n=== %s: polling arXiv ===" % now_utc())
            print_new(poll())
            print("sleeping %d seconds" % args.interval)
            time.sleep(args.interval)
        except KeyboardInterrupt:
            print("\nwatch stopped")
            return 0
    return 0


if __name__ == "__main__":
    sys.exit(main())

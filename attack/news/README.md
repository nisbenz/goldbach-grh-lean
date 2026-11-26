# news/ — arXiv monitoring

`news/monitor.py` watches arXiv for papers related to Goldbach's conjecture and appends
new ones to `news/feed.jsonl`. It is a tracker, not a claim: a paper appearing here is
**not** verified and says nothing about the status of any claim in `map/claims.json`.

Requires Python 3 only — no external packages.

## Commands

Run from the repository root (`/home/eequaled/goldbach`):

```sh
python3 news/monitor.py once                  # one poll; prints a digest of NEW entries
python3 news/monitor.py watch --interval 1800 # poll again every 1800 s (Ctrl-C to stop)
python3 news/monitor.py digest                # human-readable digest of the last 20 feed entries
```

`once` never loops. If both queries fail, it prints a warning, leaves `feed.jsonl`
and `state.json` untouched, and exits 0.

## Exact API URLs

The script issues **two** queries per poll (Atom API, newest first):

1. `http://export.arxiv.org/api/query?search_query=all:Goldbach&start=0&max_results=100&sortBy=submittedDate&sortOrder=descending`
2. `http://export.arxiv.org/api/query?search_query=ti:Goldbach&start=0&max_results=100&sortBy=submittedDate&sortOrder=descending`

In Python source these are split across concatenation, but the resulting URLs are exactly
those above. A browser `User-Agent` is sent. Each query gets at most two attempts
(one retry), so a poll makes **at most 4 HTTP requests**, with a 20 s timeout each.
A failed query does not discard results from a successful one.

## Data files

- `feed.jsonl` — append-only, one JSON object per line with:
  `id` (normalised arXiv id, version stripped), `title`, `authors`, `abstract`
  (first 500 characters), `published`, `updated`, `url`, `found_at`, `keywords`
  (matched terms), and `score`.
- `state.json` — `last_run` (UTC ISO-8601), `last_seen_ids` (all ids seen so far),
  `last_new_ids` (ids added by the most recent poll), `total_entries`, and
  `feed_sha256` (checksum of `feed.jsonl` after the poll).

Deduplication is by arXiv id against both the feed and `last_seen_ids`. New entries are
sorted by `score` descending, with `published` descending as tie-break, before being
appended. `digest` shows the last 20 lines in stored order.

## Relevance scoring

`score` is the number of case-insensitive keyword occurrences in **title + abstract**.
A match counts a singular, plural, or possessive form. Keywords:
`goldbach`, `chen`, `sieve`, `prime`, `exceptional set`, `GRH`, `liu`,
`fundamental lemma`, `circle method`, `additive`.
This is a triage signal only — high score does not mean the result is sound or relevant.
Follow the honesty rules in `ARCHITECTURE.md`; log any failure with its derived rule in
`failures.md`.

## Scheduling suggestions

**cron** (every 30 minutes; poll output goes to a log outside the repo):

```cron
*/30 * * * * cd /home/eequaled/goldbach && /usr/bin/python3 news/monitor.py once >> /tmp/goldbach-news-cron.log 2>&1
```

**systemd user units** — `~/.config/systemd/user/goldbach-news.service`:

```ini
[Unit]
Description=GOLDBACH ATTACK arXiv news poll

[Service]
Type=oneshot
WorkingDirectory=/home/eequaled/goldbach
ExecStart=/usr/bin/python3 /home/eequaled/goldbach/news/monitor.py once
```

`~/.config/systemd/user/goldbach-news.timer`:

```ini
[Unit]
Description=Poll arXiv news every 30 minutes

[Timer]
OnCalendar=*:0/30
Persistent=true

[Install]
WantedBy=timers.target
```

Enable with `systemctl --user daemon-reload` then
`systemctl --user enable --now goldbach-news.timer`.

## Verification (2026-11-26)

Two single polls were run from the repository root:

- First `once`: both queries succeeded, 200 Atom entries parsed, **134 unique new
  entries** written (2 HTTP requests; no retries needed).
- Second `once`: both queries succeeded, 134 parsed, **0 new entries** — dedupe by arXiv
  id confirmed.
- `digest` printed the expected tail of 20 entries.

No continuous polling is running.

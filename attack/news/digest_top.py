#!/usr/bin/env python3
"""Rank arXiv feed entries by relevance to the *blockers* in map/blockers.json.

Prints a compact priority table: score, id, title, matching blockers (by keyword overlap).
Usage: python3 news/digest_top.py [--n 20]
"""
import argparse, json, pathlib, re

ROOT = pathlib.Path(__file__).resolve().parent.parent

BLOCKER_KEYWORDS = {
    "B-001": ["lean", "formal", "verify", "proof assistant", "mathlib"],
    "B-002": ["grh", "exceptional", "density", "zero", "pointwise", "goldbach"],
    "B-003": ["parity", "sieve", "chen", "level", "fundamental lemma"],
    "B-004": ["ratio", "kloosterman", "conductor", "dirichlet", "gou", "pascadi", "li"],
    "B-005": ["erh", "grand rh", "automorphic", "parity", "subcritical"],
    "B-006": ["comput", "verif", "certificate", "sieve", "prime"],
    "B-007": ["oliveira", "10^18", "comput", "verified", "range"],
    "B-008": ["survey", "news", "preprint"],
}

def text_of(e):
    return (e.get("title","") + " " + e.get("abstract","")).lower()

def main(n):
    news = []
    p = ROOT / "news/feed.jsonl"
    if p.exists():
        for line in p.read_text(encoding="utf-8").splitlines():
            if line.strip():
                try: news.append(json.loads(line))
                except Exception: pass
    scored = []
    for e in news:
        t = text_of(e)
        hits = [bid for bid,kws in BLOCKER_KEYWORDS.items() if any(k in t for k in kws)]
        scored.append((len(hits)*10 + e.get("score",0), e, hits))
    scored.sort(key=lambda x:x[0], reverse=True)
    print(f"{'rank':<5}{'pri':<5}{'id':<14}{'blockers':<24}title")
    for i,(pri,e,hits) in enumerate(scored[:n],1):
        print(f"{i:<5}{pri:<5}{e.get('id',''):<14}{','.join(hits):<24}{e.get('title','')[:88]}")

if __name__ == "__main__":
    ap = argparse.ArgumentParser(); ap.add_argument("--n", type=int, default=20)
    a = ap.parse_args(); main(a.n)

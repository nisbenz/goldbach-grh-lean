#!/usr/bin/env python3
"""Generate a static dashboard for the GOLDBACH ATTACK from the framework's JSON/JSONL state.

Usage: python3 site/build.py [--out site/dist]
"""
import argparse, html, json, pathlib, datetime

ROOT = pathlib.Path(__file__).resolve().parent.parent

def load_json(path, default):
    try:
        return json.loads((ROOT / path).read_text(encoding="utf-8"))
    except Exception:
        return default

def load_jsonl(path):
    out = []
    p = ROOT / path
    if p.exists():
        for line in p.read_text(encoding="utf-8").splitlines():
            if line.strip():
                try: out.append(json.loads(line))
                except Exception: pass
    return out

def esc(x): return html.escape(str(x))

def status_badge(s):
    colors = {"checked":"#2e7d32","conditional":"#f9a825","open":"#1565c0","refuted":"#c62828",
              "dead":"#616161","stalled":"#827717","external":"#6a1b9a","resolved":"#2e7d32"}
    return f'<span style="background:{colors.get(s,"#555")};color:white;padding:1px 7px;border-radius:4px;font-size:12px">{esc(s)}</span>'

def build(out):
    out.mkdir(parents=True, exist_ok=True)
    claims = load_json("map/claims.json", {"claims":[]}).get("claims", [])
    blockers = load_json("map/blockers.json", {"blockers":[]}).get("blockers", [])
    feed = load_jsonl("map/feed.jsonl")
    news = load_jsonl("news/feed.jsonl")
    leases = load_json("desk/state.json", {"leases":[]}).get("leases", [])
    now = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d %H:%M UTC")

    status_counts = {}
    for c in claims: status_counts[c.get("status","?")] = status_counts.get(c.get("status","?"),0)+1

    rows = "\n".join(
        f"<tr><td>{esc(c['id'])}</td><td>{esc(c.get('statement','')[:180])}</td>"
        f"<td>{status_badge(c.get('status','?'))}</td><td>{esc(c.get('hypothesis','—'))}</td>"
        f"<td>{esc(c.get('source',''))}</td></tr>" for c in claims)
    brows = "\n".join(
        f"<tr><td>{esc(b['id'])}</td><td>{esc(b['title'])}</td><td>{esc(b.get('program',''))}</td>"
        f"<td>{esc(b.get('status',''))}</td><td>{esc(b.get('difficulty',''))}</td>"
        f"<td>{esc(b.get('parallel',''))}</td><td>{esc(b.get('why',''))}</td></tr>" for b in blockers)
    nrows = "\n".join(
        f"<tr><td>{esc(n.get('published','')[:10])}</td><td>{esc(n.get('score',''))}</td>"
        f"<td><a href='{esc(n.get('url',''))}'>{esc(n.get('title',''))}</a></td></tr>"
        for n in sorted(news, key=lambda x:x.get("score",0), reverse=True)[:30])
    frows = "\n".join(
        f"<tr><td>{esc(e.get('at','')[:19])}</td><td>{esc(e.get('kind',''))}</td>"
        f"<td>{esc(e.get('by',''))}</td><td>{esc(e.get('text',''))}</td></tr>"
        for e in reversed(feed[-40:]))

    html_doc = f"""<!doctype html><html><head><meta charset='utf-8'><title>GOLDBACH ATTACK</title>
<style>body{{font:15px system-ui,sans-serif;max-width:1200px;margin:2em auto;padding:0 1em;color:#222}}
table{{border-collapse:collapse;width:100%;font-size:14px}}td,th{{border:1px solid #ddd;padding:6px 8px;text-align:left;vertical-align:top}}
th{{background:#f5f5f5}}h1{{letter-spacing:.04em}}small{{color:#666}}</style></head><body>
<h1>GOLDBACH ATTACK</h1><small>Local coordinated attack framework · generated {esc(now)}</small>
<h2>Counts</h2><p>Claims: {esc(status_counts)} · Blockers: {len(blockers)} · Active leases: {len(leases)} · News items: {len(news)}</p>
<h2>Claims</h2><table><tr><th>id</th><th>statement</th><th>status</th><th>hypothesis</th><th>source</th></tr>{rows}</table>
<h2>Blockers (attack queue)</h2><table><tr><th>id</th><th>title</th><th>program</th><th>status</th><th>difficulty</th><th>parallel</th><th>why</th></tr>{brows}</table>
<h2>Latest news</h2><table><tr><th>published</th><th>score</th><th>title</th></tr>{nrows or '<tr><td colspan=3>none yet — run news/monitor.py once</td></tr>'}</table>
<h2>Activity feed</h2><table><tr><th>at</th><th>kind</th><th>by</th><th>text</th></tr>{frows}</table>
<hr><small>Binary Goldbach is OPEN. No claim here says otherwise unless marked checked with a verifying run.</small>
</body></html>"""
    (out / "index.html").write_text(html_doc, encoding="utf-8")
    print(f"wrote {out/'index.html'} ({len(html_doc)} bytes)")

if __name__ == "__main__":
    ap = argparse.ArgumentParser(); ap.add_argument("--out", default="site/dist")
    a = ap.parse_args(); build(pathlib.Path(a.out))

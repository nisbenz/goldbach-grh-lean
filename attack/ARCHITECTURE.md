# GOLDBACH ATTACK — architecture

A local, pequalnp-style coordinated attack framework. Target: track every claim and blocker on
the route to deciding binary Goldbach, monitor all relevant news, and let agents attack blockers
with independently checked outputs. **We never claim a resolution without a checked proof or a
checked refutation.**

## Programs (like pequalnp's library/gct/meta/etc.)

| key | name | aim |
|---|---|---|
| `found` | Foundations & formalization | checked statements, Lean defs, axiom audits |
| `cond` | Conditional results | GRH/ERH/Grand-RH routes, weak Goldbach, density-one |
| `analytic` | Analytic blockers | exponential sums, zeros, ratios, Bessel/L² routes |
| `sieve` | Sieve blockers | Chen sets, level of distribution, weights |
| `comput` | Computational verification | finite checks, certificates, GPU sieve |
| `redteam` | Countermodel / refutation | parity models, reflection holes, obstruction searches |

## Status vocabulary

`checked` — kernel-checked by Lean (no sorry, allowed axioms only) or independently re-derived.
`conditional` — proof valid *assuming* GRH/ERH/etc.; recorded with the exact hypothesis.
`open` — real blocker, attackable.
`refuted` — a claimed route has a checked counterexample.
`dead` — tried and ruled out by a cited argument (graveyard).
`stalled` — partial result, no progress.

## State files (all human-readable JSON/JSONL)

- `map/claims.json` — every claim: id, statement, status, imports/source, deps, first/last activity.
- `map/blockers.json` — open blockers with attack routes, difficulty, deadlines.
- `map/feed.jsonl` — append-only event log (claim_checked, blocker_opened, attack_started, etc.).
- `desk/state.json` — leases (id, holder, expires, beat count).
- `news/feed.jsonl` — arXiv/news entries with ids, titles, relevance.
- `failures.md` — every failure with root cause + derived rule (like pnp_failures.md).

## Components

1. `news/monitor.py` — poll arXiv API + repo commits; write news/feed.jsonl; dedupe.
2. `desk/desk.py` — commands: `next`, `beat`, `release`, `submit`, `verdict`, `status`.
   Local file-based leases (45 min, renew every 30, 6 h max) mirroring pequalnp desk rules.
3. `checker/check.py` — run Lean build + axiom audit on a submitted file, plus the repo's
   Python interval verifiers; verdict ACCEPTED/REJECTED/FAULT with a log.
4. `site/build.py` — generate static HTML (index, map, news, contributors, graveyard) from JSON.
5. `agents/GUIDE.md` — mandatory subagent instructions (exact statement, build/verify, honest
   partials, no git ops, parent re-verifies).

## Honesty rules

1. No unverified claims. Every number gets a source or a check command.
2. The cloned repo's claims are AUDITED first (`audit/REPO_AUDIT.md`) — nothing inherited as
   checked without a passing `lake build` / verifier run or an explicit "not yet verified" label.
3. Conditional ≠ unconditional. Every conditional theorem carries its hypothesis in the claim id.
4. Failures logged with the rule derived from them. No silent retries.

## What "know if Goldbach is true or false" means operationally

We attack blockers until either (a) a `checked` proof of the binary statement exists in our map,
or (b) a `refuted`/`dead` result shows a route cannot work — and we report exactly what is and
isn't established. We do not assume the conjecture is true or false.

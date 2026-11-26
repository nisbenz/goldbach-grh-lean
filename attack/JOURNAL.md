# Goldbach — research journal

### 2026-11-26 — NEW TRACK started

User: "create another worktree. were not working on chess anymore. lets work on goldbach!!"
Chess track (chess-solved) and P vs NP fleet track (pequalnp-proofs) both closed out; those
directories are untouched and preserved as records.

Created fresh git repo at `/home/eequaled/goldbach` (native disk, not the slow FUSE mount).
Identity: eequaled / 215157620+eequaled@users.noreply.github.com. Initial files: README.md,
this journal, .gitignore. No commits yet.

Target direction NOT yet chosen — need user input on what "work on Goldbach" means:
formalization (Lean), computational verification, or research framework. Do not start coding
until direction is set, to avoid wasted work like the P vs NP races.

### 2026-11-26 — GOLDBACH ATTACK framework launched (user directive)

User: clone https://github.com/nisbenz/goldbach-grh-lean here; build a pequalnp-style setup for
Goldbach — "monitor all news and stuff and attack all blockers till we know if the Goldbach
conjecture is true or false."

- Repo `/home/eequaled/goldbach` created (native disk), clone at `goldbach-grh-lean/` (symlink
  `refs/goldbach-grh-lean`). Clone claims: GRH-conditional weak Goldbach, GRH binary exceptional
  set, `sorry`-free Lean v4.16.0 + Mathlib, Python interval verifiers, C++ finite verifier.
- Framework built: ARCHITECTURE.md (programs found/cond/analytic/sieve/comput/redteam; statuses),
  map/{claims,blockers}.json + feed.jsonl, site/build.py (static dashboard), agents/GUIDE.md,
  failures.md. Committed as e22a144 + 66e4bf9.
- Three subagents launched: (1) audit cloned repo (Lean toolchain/verifiers/claims/blockers),
  (2) arXiv news monitor (news/monitor.py), (3) desk + checker (desk/desk.py, checker/check.py).
- NOTHING from the clone is accepted as checked until the audit passes. Conditional results stay
  conditional. No claim that Goldbach is true or false.

### 2026-11-27 — upstream PR merged + blocker issues created
User: "PR it to nisbenz/goldbach-grh-lean ... im a contributor ... make the agents.md and mention
the blockers. tomorrow astra should make an attack on these problems."
- Packaged framework as `attack/` subtree in upstream repo (own Lean pin; original `lean/` untouched),
  root `AGENTS.md` with binding protocol + section 9 blocker handoff to Astra (11 blockers, next angles).
- PR #1 opened and MERGED into nisbenz/goldbach-grh-lean main (WRITE permission; no fork needed).
  Created 11 issues: #2 B-002, #3 B-003, #4 B-004, #5 B-005, #6 B-007, #7 B-010, #8 B-011,
  #9 B-012, #10 B-013, #11 B-014, #12 B-015. Each with status OPEN, concrete next angle,
  evidence (audit files / checked lemmas), and the desk+AGENTS.md work protocol; labelled.
- Flagged in PR: repo has no LICENSE file; vendored Apache-2.0 checker keeps its LICENSE + attribution.
- Honest state: 11 checked micro-results, 0 resolution. Binary Goldbach OPEN (also under ERH).

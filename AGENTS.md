# AGENTS.md — rigorous, persistent attack protocol for `goldbach-grh-lean`

This file is for any AI agent (or the repository owner's models) working on this repository.
It describes the system used by a collaborator's fleet in Nov 2026 to turn an open problem into a
queue of independently checkable steps. **Read it fully before touching a proof.** The goal is to
decide binary Goldbach — and to know honestly which direction is established. Nothing here claims
the conjecture is true or false.

## 0. The one non-negotiable rule

A statement counts as **checked** only when a machine check accepted a proof of *exactly* that
statement, with no `sorry`, no new axiom beyond `propext`/`Classical.choice`/`Quot.sound`, and no
`native_decide`. Everything else is a claim: conditional, external, or unverified. Never promote a
claim to checked because it "looks standard", because a paper says it, or because a previous agent
said so. Conditional results keep their hypothesis in their id and in their statement forever.

## 1. Strategy: weak first, then strong; ERH as an explicit assumption

1. **Weak (ternary) Goldbach first.** It is already proved unconditionally in the literature
   (Helfgott 2013) and this repo has a GRH-conditional formalization. Treat the repo's Lean files
   as a *candidate* to audit, not as checked until you run the build + axiom audit yourself.
   Completion criterion for this phase: a kernel-checked `WeakGoldbachConjecture` theorem, with an
   audit log, in our own map as `checked` (or, under a hypothesis, recorded as `conditional`).
2. **Assume the Extended Riemann Hypothesis (ERH) explicitly** for the strong side. The repo's
   attack docs already analyse GRH, ERH and Grand RH. User guidance (26 Nov 2026): "we suggest we
   assume the extended Riemann hypothesis too". Record ERH as a named hypothesis, never silently.
   A proof under ERH is a *conditional* result: valuable, but not a resolution of binary Goldbach.
3. **Then attack pointwise Strong Goldbach.** The repo's GRH result is only an exceptional-set
   bound `E(X) <= 2,000,000 sqrt(X) log^3 X`, i.e. density one, not `E(X)=0`. The central blocker
   is closing that gap (or proving no route can). Attack it with the queue in §3, not ad hoc.

## 2. State and tools (all local, no PRs/pushes by agents)

- `attack/ARCHITECTURE.md` — programs, statuses, honesty rules.
- `attack/map/claims.json` — claims with `status` and `hypothesis`; `attack/map/blockers.json` — attack queue;
  `attack/map/feed.jsonl` — append-only event log. Update these when you change a status.
- `attack/desk/desk.py` — file-based lease desk: `next`, `beat`, `release`, `submit`, `status`,
  `blockers`. Take a blocker before working on it; renew every 30 min; release honestly.
- `attack/checker/check.py` — quick checks (`file`, `lean`, `verifier`, `verdict`).
- `attack/checker/strict_check.py` — wraps the **vendored Apache-2.0 pequalnp checker**
  (`attack/vendor/pequalnp/tools/check-lean.mjs`): kernel re-check, axiom audit, exact-statement check.
  This is the real verdict. All runs append to `attack/checker/runs.jsonl`.
- `attack/news/monitor.py` — arXiv polling (`once`, `watch`, `digest`); `attack/news/digest_top.py` ranks papers
  against blockers. Run `once` at least daily; log actionable papers into `attack/map/feed.jsonl`.
- `attack/site/build.py` — regenerate the dashboard after state changes.
- `attack/failures.md` — every mistake logged with root cause + derived rule.

Do not edit `attack/vendor/pequalnp/` (third-party Apache code). Do not run the exhaustive verifiers
(`verify_finite` to 1e9, full ladder) without an explicit budget — they take hours.

## 3. How to attack a blocker (the loop)

1. `python3 desk/desk.py next --holder <name> [--program <key>]` — get a lease + the exact blocker.
2. Write **one** file. Prove exactly the recorded statement. No rewording, strengthening, or
   weakening. Helpers go in the same file in a private namespace.
3. Self-verify before reporting: (a) the theorem with the exact name is present — grep for it;
   a green build with only helpers is a failure; (b) the build/check passes; (c) no banned tokens;
   (d) the statement matches the recorded one byte-for-byte modulo whitespace.
4. `python3 checker/strict_check.py <file> <statement-file>` (or the subcommands in §2) and paste
   the verdict. If it fails, fix and re-check. **Never** report success on an unverified build.
5. `python3 desk/desk.py submit <lease> <file>`; append a `submitted` event to `attack/map/feed.jsonl`;
   if accepted, flip the claim/blocker status in the map only after the checker log says so.
6. If stuck: release with an honest reason (`missing_lemma`, `hypothesis_too_weak`,
   `statement_seems_false`, `does_not_elaborate`, `out_of_time`, `other`) and record the exact
   obstacle in `attack/failures.md`. A precise failure is useful work; a fabricated success is not.

## 4. Subagent discipline (when delegating)

Every delegated task MUST include: the exact statement; the requirement that the theorem be
present and the build pass; the banned-token list; honest partials with precise obstacles; no git
operations; and a checkpoint file `attack/agents/CHECKPOINT_<blocker-id>.md` updated as work proceeds.
The parent re-verifies every claim (theorem grep → build/strict check → status check) before
updating the map. A subagent silent with no file writes gets stopped and reprompted with a simpler
plan. If a blocker leaves `open` or is resolved elsewhere, stop immediately — do not keep working
on a dead task (this was learned the hard way in the P vs NP races; see §6).

## 5. News and research triage

- `python3 news/monitor.py once` — fetch new arXiv entries; dedupe is automatic.
- `python3 news/digest_top.py --n 20` — rank by overlap with our blockers.
- Treat crank-looking papers (grand claims, no citations, "solved by a new Turing machine") as
  **untrusted**: log them as noise, never as a claim or a blocker change.
- When a relevant paper appears, append a `news` event with its arXiv id and open a blocker for
  any route it suggests; verify every number taken from an abstract before using it.

## 6. Lessons inherited from the P vs NP track (do not repeat)

- A correct proof that arrives 2 minutes late is worth nothing — check `/desk/status`-equivalent
  (here: `attack/map/blockers.json` + `desk.py status`) before *and* after work.
- `decide` on a whole conjunction containing a complex predicate often fails to synthesize
  `Decidable`; split into subgoals and `simp`/`decide` each part.
- A green build with no theorem declaration is not a proof. Grep the theorem name.
- Search gaps that "either answer is wanted" are usually resolved by the negative side within
  minutes; do not sink hours into witness search without a fresh, unclaimed target.
- After a machine crash, stop all running agents and check state FIRST; stale agents work on
  consumed blockers and can produce wrong artifacts.

## 7. Licensing and PR hygiene

- `attack/vendor/pequalnp/` is Apache 2.0, copied with its LICENSE and attribution in
  `attack/vendor/pequalnp/README.md`. Keep the notice if you redistribute.
- This repository (`goldbach-grh-lean`) currently has **no LICENSE file** — ask the owner before
  adding one or opening a licensing PR; do not assume a license.
- The collaborator opening the PR should push only the agreed framework files; agents do not push.

## 8. What "true or false" means operationally

We keep attacking blockers until either a `checked` proof of binary Goldbach exists in the map, a
`checked` refutation exists, or every route is recorded `dead`/`refuted` with checked evidence —
and then report exactly what is established. Until then, the answer is **open**, including under
ERH. Never write "we proved Goldbach" unless the checker log says so.

---

## 9. Live blocker inventory (as of 2026-11-27) — handoff to the next agent (Astra)

The attack queue is `attack/map/blockers.json` (11 open). The checked ground is recorded in
`attack/map/claims.json` (11 `checked` claims). **Binary Goldbach remains OPEN.** Use
`python3 attack/desk/desk.py next --holder <name> --id <blocker-id>` to lease a specific one;
the desk has an `--id` flag (added after `--hard` mis-targeted agents). Renew with `beat` every
30 min, release with an honest reason when done. All files and logs are local; agents do not push.

### Checked ground already established (do NOT redo)
- `GB-DEFS` — exact Lean definitions of binary/weak/up-to/from Goldbach.
- `GB-FINITE-10000` — kernel-checked prime-pair witnesses for every even 4 <= n <= 10000.
- `GB-H1-CERT` / `GB-H1-CONSTS` / `GB-H1-CORE` — H1 major-arc rational certificate, constants,
  and the Lean lemma "positive prime-pair coefficient => Goldbach".
- `GB-DYADIC`, `GB-B017`, `GB-B013-PART`, `GB-PSI-THETA` — dyadic bound, Liouville detector,
  reflection-hole witness (Z/32Z), finite prime-power bound.
- `GB-B011-PHASE`, `GB-B010-L2` — kernel-checked micro-lemmas from the two analytic blockers below.
- Audits: `attack/audit/REPO_AUDIT.md` (this repo's Lean claims: 17 axioms, "zero axioms" REFUTED;
  numeric verifiers PASS; v4.16.0 `lake build` UNVERIFIED), `attack/audit/ERH_ROUTE_ANALYSIS.md`,
  `attack/audit/B003_PARITY_ANALYSIS.md`, `attack/audit/B010_MEANSQUARE_ANALYSIS.md`,
  `attack/audit/B011_ZEROPAIR_ANALYSIS.md`.

### The hard blockers (all OPEN — no proof, no refutation)
| id | program | blocker | concrete next angle from the analyses |
|---|---|---|---|
| B-002 | analytic | Pointwise Strong Goldbach beyond exceptional set (E(X)/X -> 0, not E(X)=0) | H3 centering (Theorem 3); signed minor-arc criterion H1/H2/H3 |
| B-003 | sieve | Parity countermodel: weights pass divisor tests for every level <1 yet contain no primes | numeric model (X=1e5) shows bilinear B+/U+ = 1 exactly; need an INDEPENDENT bilinear theorem for genuine Lambda coefficients |
| B-004 / B-014 | analytic | GWX Dirichlet 2/2 ratios: q^(1-2eta) conductor barrier | moving-line / finite-endpoint one-sided criteria; arXiv:2611.18825v1 (supplied, unverified) |
| B-005 | cond | Automorphic-RH parity survival + Grand RH | parity survival theorem survives; do not assume it closes the gap |
| B-007 | comput | Independent re-verification of the 4e18 finite claim | distributed/certificate-based check; our kernel-checked range is only 1e4 |
| B-010 | analytic | 1/4 mean-square exponent gap | L2->sup artifact; need mean-square exponent alpha<2 (currently 5/2); L2-budget lemma checked, analytic improvement open |
| B-011 | analytic | Zero-pair T^(3/2)log^2T block | Stirling confirms block; survives ERH/Grand RH; need signed two-input estimate retaining common phase; phase-sum lemma checked |
| B-012 | sieve | Bilinear test with strict domination | directly follows B-003: show genuine Lambda coefficients beat the parity model |
| B-013 | redteam | Fourier reflection hole in Z/MZ | convolution-zero witness in Z/32Z checked; Fourier-smallness still open |
| B-015 | sieve | Li-Liu (1+1.9) narrowing to a=1 | divergence as b->1; new supply estimates carrying parity |

### Honest summary for Astra
ERH is already what the repo calls Dirichlet GRH, so assuming it adds **no** new exponent.
Pointwise Strong Goldbach is open even under ERH. Every one of the 11 checked claims is a finite
or combinatorial piece; none proves the conjecture. Keep the loop: take a lease, prove exactly
the stated micro-claim, run `attack/checker/strict_check.py`, update the map only when a check
passes, log failures in `attack/failures.md`, and never claim resolution without a checked proof.

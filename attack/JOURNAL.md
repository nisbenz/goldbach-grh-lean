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

### 2026-11-27 — Astra Orchestration Wave 0 & Wave 1 (Strong Goldbach attack)
- Fast-forward pulled `origin/main` (`9686403..518aca1`), refreshed arXiv monitor (134 entries, 0 new).
- **Wave 0 (`B-016` RESOLVED):** Verified original `lean/` (`v4.16.0`) builds cleanly (`check.py lean` ACCEPTED, runs `54d1f6bc` and `87f2e805`); captured exact `#print axioms` (`weak_goldbach_theorem`: 7 declared axioms; `binary_goldbach_exceptional_bound` & `binary_goldbach_density_one`: 11 declared axioms). Both remain `conditional`.
- **Wave 1 (5 parallel `gpt-6.2-astra` agents, all parent re-verified, all leases released, all GitHub issues `#2, #4, #5, #9, #10, #11, #12` updated):**
  - `B-002` (`B002_ASTRA_CENTERING_ATTACK.md`): certified H3 RH loss `< 1.05e-7`, scanned all 24,999 even `N <= 50000` (`u_N < 0` on 24,967 targets, min `-0.456535`), proved negative PNT average of `U_N`, compiled `reflection_energy` + `centered_expansion` in Lean v4.16.0.
  - `B-004`/`B-014` (`B004_B014_GWX_RATIOS_ATTACK.md`): re-derived all 3 cutoff optima & Bettin–Chandee (`<0.608` vs `theta>2`), verified 39 targets + 25 eq.(16) + 28 PSD cases in 160-bit Arb, audited 4 bypass routes; recommended consolidating analytic work under `B-004`.
  - `B-012` (`B012_BILINEAR_PARITY_ATTACK.md`): genuine rough `B/S in [-0.343, -0.316]` vs `+1` for `a^+`; **proved unconditionally (PNT + `lambda(k)` projection) that centered dispersion off-diagonal `O_pm >> N^(3/2)` on `2^t` for BOTH parity models**, while genuine `O < 0` on all 5 targets (with `V` 66x smaller at `N=131072`).
  - `B-013` (`B013_REFLECTION_HOLE_ATTACK.md`): derived sharp Hoeffding bound `sqrt(1 + (M/2) log M)` for all even `M>=4`, verified 16 largest-conductor unit holes (`E-O = -g^2`), proved fiber prime-count surplus fails for all `2p^2` with `p > 1190`, compiled `reflection16_lower_tests` in Lean v4.16.0.
  - `B-015`/`B-005` (`B015_B005_SIEVE_NARROWING_ATTACK.md`): **sharpened Selberg constant in (13) from 200 to 8** (`b = 1.899989 / 1.39890` given `[U]` Li-Liu supply), proved parity-model loss `liminf >= log((a-1)/(b-1))`, scanned all 249,999 even `N <= 500000` for `H(N)` & Chen/Li-Liu biases, compiled `subcritical_marked_divisor` in Lean v4.16.0.
- **Honest state:** 15 checked finite/algebraic claims (including 3 newly v4.16.0-checked micro-lemmas + H3 margin); 11 open blockers remain open; Binary Goldbach remains **OPEN** (including under ERH). Proceeding to Wave 2 (`B-003`/`B-012` dispersion-projection follow-up, `B-010`/`B-011` multi-conductor zero-pair & higher-moment attack, and `B-007` computational verification audit).

### 2026-11-27 — Astra Orchestration Wave 2 (All 11 open blockers now deeply audited & attacked)
- **Wave 2 (3 parallel `gpt-6.2-astra` agents, all parent re-verified, all leases released, issues `#3, #6, #7, #8, #9` updated):**
  - `B-011`/`B-010` (`B010_B011_ASTRA_ZEROPAIR_MOMENTS.md`):
    - **Key analytic progress on B-011:** Proved via Euler's Beta integral + smooth localization around stationary points + Cauchy–Schwarz + local zero density that the full-line positive-ordinate dyadic block is bounded by `O(T log(2dT) log(2d'T))` uniformly in `N` under ERH — **saving a full factor of `sqrt(T)`** over the repo's `T^(3/2) log^2 T` triangle estimate! Proved exponential suppression on finite arcs (`|K_U| <= 2 asinh(U) exp(-h arctan(1/U))`).
    - **Key analytic result on B-010:** Proved sharp `L^p` moment power `beta(p) = p + 1/2` for the companion norm inputs (single-coefficient powers `5/4, 9/8, 13/12 -> 1`, direct `L^1` gives `2 N log N`), with an explicit modulated-interval witness hitting `-N`. Compiled `momentBudget` in Lean v4.16.0.
  - `B-003`/`B-012` (`B003_B012_ASTRA_DISPERSION_PROJECTION.md`):
    - Scanned 315 targets up to `2^20`: corrected Wave 1's small-sample sign impression — `O_true` is negative on powers of two (`2^14..2^20`) but strongly positive on all 9 highly composite/primorial multiples (`+4,051,562` at `510510` vs HL covariance prediction `+3,855,044`; HL predictor matches 273/288 signs, `r=0.925`). Proved `O >= -D >> -N log^2 N` and the exact left-prime erasure obstruction for `d,k>1` boxes. Compiled `weighted_prime_mass_cuberough`, `exists_positive_prime_of_cuberough_strict`, and `b004_dyadic_projector` in Lean v4.16.0.
  - `B-007` (`B007_COMPUTATIONAL_VERIFICATION_AUDIT.md`):
    - Independent native verification up to `5*10^7` in `0.0917s` (max `p_min = 1039` at `37,998,938`), cross-checked by 30-wheel CPU & HIP GPU, plus full unmemoized replay of all 2,501 Pratt ladder certificates (86,507 nodes).
    - **Caught real bug in `verify/verify_finite.cpp`:** unsigned underflow at `M=6, L=99` produces a false PASS (`p_k = 18446744073709551557`).
    - **Built packed Lean v4.16.0 certificate** proving `BinaryGoldbachUpTo 10000` in `5.51s` (exact-type kernel replay `5.38s`, 15.6KB bound-specific source vs 511KB legacy, allowed axioms only). Estimated full `4e18` re-verification at ~1,803 whole-node-years at the high-window CPU rate.
- **Honest experiment state after Waves 0–2 (8 Astra runs, 100% of open blockers audited):**
  - **19 checked finite/algebraic claims** (11 baseline + 8 newly parent-verified across Lean v4.16.0 & exact rational arithmetic).
  - **1 resolved blocker (`B-016`)**, **11 open blockers** (`B-002`, `B-003`, `B-004`, `B-005`, `B-007`, `B-010`, `B-011`, `B-012`, `B-013`, `B-014`, `B-015`).
  - **Binary Goldbach remains OPEN (including under explicit ERH).** Every analytic, sieve, spectral, and red-team route converges on the same irreducible barrier: a pointwise, two-input, signed estimate for genuine `Lambda` that breaks parity/reflection symmetry at a single specified even target `N`.

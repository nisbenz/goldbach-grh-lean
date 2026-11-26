# Checkpoint — B-002 (ERH route research analysis)

- Date: 2026-11-26 (session date from harness; repo protocol date)
- Holder: subagent (research analysis only; no lease taken via `desk.py`)
- Mode: READ-ONLY on git; writes restricted to
  `audit/ERH_ROUTE_ANALYSIS.md`, `agents/CHECKPOINT_B-002.md`, scratch
  `/tmp/opencode/goldbach_erh/`.

## Status
COMPLETE — analysis written; no proof claimed, no map status changed.
B-002 remains `open`.

## Read so far
1. `AGENTS.md` (full, 111 lines) — binding protocol; §0 checked-only rule, §4 subagent discipline, §8 "open including under ERH".
2. `ARCHITECTURE.md` (full, 60 lines).
3. `audit/REPO_AUDIT.md` (full, 368 lines) — 35 claims; axiom audit (17 axioms); 25-blocker catalogue; exact hypotheses table (§5).
4. `map/blockers.json` (read-only) — B-002 is `open`, difficulty `hard`, program `analytic`; related B-010/B-011/B-005.
5. `goldbach-grh-lean/proof/strong_goldbach_erh_attack.md` (full, 204 lines) — eqs (1)–(9), automorphic parity theorem, LWW support computation, Chen reduction.
6. `goldbach-grh-lean/proof/strong_goldbach_research.md` (full, 214 lines) — H1/H2/H3, 1/4 mean-square gap, zero-pair kernel (4), T^{3/2}log²T, parity/reflection countermodels.
7. `goldbach-grh-lean/proof/weak_goldbach_proof.md` lines 1–12 — exact GRH wording: "every nontrivial zero of every primitive Dirichlet L-function, including the Riemann zeta function".
8. Mathlib cache `/home/eequaled/lean-lake-cache/packages/mathlib/Mathlib/`:
   - `NumberTheory/LSeries/RiemannZeta.lean:185` defines `RiemannHypothesis : Prop` (zeta only).
   - `NumberTheory/LSeries/Dirichlet.lean` header: Dirichlet L-series API, nonvanishing for `re s > 1` only; NO RH/GRH definition.
   - `NumberTheory/ArithmeticFunction/Liouville.lean:27-31` defines `liouville`, `liouville_apply`.
   - `NumberTheory/ArithmeticFunction/Misc.lean:258-267` defines `cardFactors`/notation `Ω n = n.primeFactorsList.length`.
   - Grep across all cached packages: only zeta `RiemannHypothesis` in Mathlib; no `ERH`/Dirichlet-GRH def.
9. AINTLIB sibling (not Mathlib): `DedekindResidue/DedekindResidue/CompletedZeta/GRH.lean:40-42` defines `GeneralizedRiemannHypothesis (K)` for Dedekind zeta as nonvanishing on `Re>1/2` away from pole — precedent for threading GRH as a hypothesis, not an axiom.

## Key preliminary findings (all to be labelled in final doc)
- The repo's "Dirichlet GRH" IS ERH on the Dirichlet family; assuming ERH explicitly adds no new exponent to the repo's circle-method error terms. Genuinely stronger hypotheses would be Artin/Dedekind GRH or Grand RH (automorphic).
- 1/4 gap: mean-square `≤1600N^{5/2}L³` → single-coefficient allowance `40N^{5/4}L^{3/2}`; positivity needs `~N`; gap exactly 1/4.
- Zero-pair block: `T^{3/2}log²T` from `asymp T^{-1/2}` gamma quotient × `(T log T)²` pairs; at `T≈N` needs `N^{1/2}log²N` saving.
- Docs do NOT claim ERH closes pointwise Goldbach; parity/reflection obstructions survive as failures of specified deductions, not logical independence.

## Files written (measured with `wc -c -l -w`)
- `audit/ERH_ROUTE_ANALYSIS.md` — 24,125 bytes, 422 lines, 3,444 words.
- `agents/CHECKPOINT_B-002.md` — 3,887 bytes, 47 lines (this file, final).

## Closing notes
- Analysis contains: labelled [Q]/[P]/[I]/[SRC]/[U] claims; ERH definition and
  Mathlib search result (only zeta `RiemannHypothesis`); exact exponent ledger;
  one proposed micro-blocker B-017 (Liouville prime-detector identity, easy–
  medium, NOT proved); honest verdict (open under ERH; obstruction survives as
  failure of specified deductions, not independence).
- No Lean build, no checker run, no git operation by this subagent; no file
  under `map/`, `lean/`, `desk/`, `checker/`, `news/` or the cloned repo touched.
- No success claim about Goldbach; no status flip.

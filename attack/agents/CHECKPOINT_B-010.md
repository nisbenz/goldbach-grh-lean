# Checkpoint — B-010 (1/4 mean-square exponent gap)

**Date:** 2026-11-26. **Holder/author:** agent-b010 (subagent). **Mode:** read-only research analysis; no proof claim.

## Lease status (honest)
- Ran `python3 desk/desk.py next --holder agent-b010 --program analytic --hard`.
- It returned **B-004** ("GWX Dirichlet 2/2 ratios and the q^(1-2eta) barrier"), **not B-010**.
  Cause [I]: desk `--hard` sorts by difficulty rank descending, stable on ties; B-004 and
  B-010 are both `difficulty: research` (rank 4), and B-004 precedes B-010 in
  `map/blockers.json` file order. `next` has no option to target a specific blocker id.
- **Released** B-004 immediately: lease `ca7269cd4ab54041816852c36c00e8cb`, reason
  `wrong_blocker: leased B-004 but delegation targets B-010 ...`. Desk confirmed `"status": "released"`.
- B-010 is confirmed `open` in `map/blockers.json` (`parallel: 5`, `difficulty: research`).
- No B-010 lease is held; the delegated work is a read-only analysis, so no lease is required
  to write the two permitted files. No desk state touched except the `next`/`release` CLI.

## Progress
- [x] Read `AGENTS.md`, `ARCHITECTURE.md`, `audit/REPO_AUDIT.md`, `audit/ERH_ROUTE_ANALYSIS.md`.
- [x] Read source `goldbach-grh-lean/proof/strong_goldbach_research.md` §2 (line 98: [Q] mean-square quote).
- [x] Read companion `goldbach-grh-lean/proof/binary_goldbach_exceptional_proof.md` Lemma 1
      (lines 27-31: derivation of `1600 X^{5/2} L^3`) and Lemma 6 (lines 63-67: Markov count).
- [x] Exact arithmetic verified with Python: `2*20^2*2 = 1600`; `1600*16^2 = 409600`;
      dyadic factor `410000/(1-2^{-1/2}) = 1399827.56 < 2e6`; exponents `alpha/2=5/4`,
      `(alpha-1)/2=3/4`; needed `alpha<2` for sup o(N).
- [x] Located Mathlib anchor for proposed Lean lemma: `Finset.single_le_sum`, precedent at
      `Mathlib/Algebra/Polynomial/UnitTrinomial.lean:194` (`single_le_sum (fun k _ => sq_nonneg ...)`).
- [x] Write `audit/B010_MEANSQUARE_ANALYSIS.md` (done; 18,449 bytes).
- [x] Final size report + close. `agents/CHECKPOINT_B-010.md` = 2,497 bytes (before this
      final size note). Desk check: `active_lease_count: 0`, `active_leases: []` — no lease held.
  Banned-token scan of the analysis: only one literal `sorry`, explicitly a PROPOSAL
  PLACEHOLDER in §3.2 (labelled proposed/unverified, not a submitted proof); no
  `native_decide`/`admit`/`unsafe`/`opaque`/`implemented_by` in submitted claims.

## Scope discipline
- Writes restricted to this checkpoint and `audit/B010_MEANSQUARE_ANALYSIS.md`; scratch in `/tmp/opencode/b010/`.
- No git operations, no map/lean/desk(except CLI)/checker/news/cloned-repo modification.
- No arXiv PDF fetching; all task items done from local sources only.

## Honesty
- Nothing here is `checked` under AGENTS.md §0. All numbers are tagged [Q]/[P]/[I]/[U].
- No claim that Goldbach is true/false; no claim that the 1/4 gap is closed.

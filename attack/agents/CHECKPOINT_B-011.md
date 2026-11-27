# Checkpoint — B-011 (Zero-pair T^(3/2) log^2 T block)

**Date:** 2026-11-26. **Holder label:** agent-b011 (research-analysis subagent).
**Git:** read-only. No commits, pushes, PRs, or clone modifications.

## Desk / lease status (honest, recorded first)

- Required command was run verbatim:
  `python3 desk/desk.py next --holder agent-b011 --program analytic --hard`.
- It returned **B-004** (`GWX Dirichlet 2/2 ratios and the q^(1-2eta) barrier`,
  lease `1d4a67b401ab44b788a5e73d16752e4a`), **not B-011**.
- Per delegation instruction that case: the B-004 lease was **released immediately**
  with reason `other: delegation targets B-011 but next returned B-004; no work done`.
- Verified via `desk.py status` / `desk.py blockers`: B-011 is `open`, program
  `analytic`, difficulty `research`, `parallel 5`, `assigned_to: null`; no active
  leases at all. The desk `next` command has no blocker-id selector, so no valid
  B-011 lease was obtained. **No further `next` calls were made** (avoided lease
  churning / grabbing an unrequested blocker).
- **Consequence:** this work is a read-only research analysis explicitly delegated
  for B-011, NOT a lease-backed attack. **No claim/blocker status was changed;**
  `map/`, `lean/`, `checker/`, `news/` and the cloned repo were not written to.
  The parent must decide whether to accept the analysis under a fresh proper lease.

## Progress log

- [x] Read `AGENTS.md`, `ARCHITECTURE.md`, `audit/REPO_AUDIT.md`,
      `audit/ERH_ROUTE_ANALYSIS.md` in full.
- [x] Read primary source `goldbach-grh-lean/proof/strong_goldbach_research.md`,
      §2 lines 96–118 (kernel (4), Stirling bound, T^(3/2) log^2 T claim, caveat).
- [x] Derived gamma-quotient modulus via Stirling with full exponent arithmetic
      (e^{-π(γ+γ')/2} cancellation; result √(2π)/√(γ+γ') ≍ T^{-1/2}).
- [x] Pair count in [T,2T]: (T log T)^2 pairs × T^{-1/2} = T^{3/2} log^2 T —
      doc's exponent **confirmed** for the absolute-magnitude (triangle) sum.
- [x] Identified one PROPOSED checkable micro-step (finite geometric-sum phase
      cancellation lemma; unit-modulus sub-fact already exists in Mathlib as
      `Complex.norm_exp_ofReal_mul_I`, `[simp]`).
- [x] Optional numerical diagnostic run in scratch with mpmath 1.3.0 (first 100
      zeta zeros); results are [I]-labelled and are NOT a proof.
- [x] Wrote `audit/B011_ZEROPAIR_ANALYSIS.md` (sizes recorded at close below).

## Honest partials / obstacles

- No Lean build was attempted; no `checker/strict_check.py` run; the micro-step is
  PROPOSED, not checked.
- The actual signed pair sum is not computed analytically; only the absolute
  magnitude (triangle bound) is verified. Cancellation is observed numerically
  on a tiny, non-asymptotic sample, not proved.
- No status flip, no submission, no beat (no valid lease to renew).

## Files written (this agent, only these two)

- `agents/CHECKPOINT_B-011.md`
- `audit/B011_ZEROPAIR_ANALYSIS.md`

Final byte sizes (measured at close):
- `agents/CHECKPOINT_B-011.md` = 3,681 bytes
- `audit/B011_ZEROPAIR_ANALYSIS.md` = 21,062 bytes

State re-check after work (`desk.py status`): B-011 still `open`,
`active_lease_count = 0`, `held_counts = {}`, `submission_count = 1` (unchanged
from before). `git status --short` shows modifications only to `desk/leases.jsonl`
and `desk/state.json` (side effects of the required lease take + release via the
desk CLI) plus the two files above. Other untracked files present in the worktree
(`CHECKPOINT_B-003.md`, `CHECKPOINT_B-010.md`, `B010_MEANSQUARE_ANALYSIS.md`,
`lean/Goldbach/Finite50000.lean`) belong to other concurrent agents and were
**not** created or touched by this agent.

## Wave 2 — Astra (astra-w2-b011)

- [Q] 2026-11-27. Issues #8 and #7 open at intake. B-011 lease `de3b1451cb124887993d765bc1730546`. Investigating finite arcs, positive-ordinate blocks, and the companion Fourier moment budget.
- [P] Full-line beta-integral argument gives a uniform-in-target positive dyadic bound of order T times the two local zero-density factors. Fixed finite arcs exponentially attenuate high blocks. Reproducible calculations cover 1,561 zeta ordinates and 278 ordinates from four primitive nonprincipal characters. The complete report includes the aggregate finite-arc diagnostic.
- [P] For the companion dissection the sharp abstract moment power is p+1/2. A modulated interval example saturates it. The real-exponent budget and Markov conjunction compiled in Lean 4.16.0 and passed a separately typed import test. [Q] The vendored checker rejected the external scratch module at its project-path gate.
- [Q] Closing findings posted on [#8](https://github.com/nisbenz/goldbach-grh-lean/issues/8#issuecomment-7223611762) and [#7](https://github.com/nisbenz/goldbach-grh-lean/issues/7#issuecomment-7223613576). Lease `de3b1451cb124887993d765bc1730546` released with reason `missing_lemma`. Subsequent desk and issue checks confirmed both blockers open and this lease absent. [U] The missing lemma controls the signed complementary coefficient at the specified even target.

## Wave 3 — Astra (astra-w3-b011)

[Q] Leased open B-011 and posted the start on issue #8. Investigating the derivative in the zero-block duality, the conductor cost on Farey arcs, and the moment threshold for the companion model.

[P] Localizing the differentiated explicit formula saves one logarithm for natural weights at height comparable to the target. On the actual Farey cells the squared norm of the height-T field is at most a constant times (N/T) log²(2QT), by shell localization and center orthogonality. Removing ordinates above log⁴ N therefore costs o(N) even with the mixed terms. The companion model has a global error-norm floor from the different leading constants in its two energies. Writing the derivations and limitations.

[P] Completed [the Wave 3 report](../audit/B011_W3_PERSISTENT_BETA_PUSH.md). Its finite beta identity agreed with independent quadrature to 7.92e−15. [U] The signed low-height residual lacks the H1/H2 margin. No blocker-level proof or checker submission.

[Q] Lease released with reason `missing_lemma`. Results posted on [#8](https://github.com/nisbenz/goldbach-grh-lean/issues/8#issuecomment-7224308432) and [#2](https://github.com/nisbenz/goldbach-grh-lean/issues/2#issuecomment-7224308750).

## Wave 4 — Astra (astra-w4-lowzeros)

[Q] Leased B-011 (`1a44320887bb4a9b97f300090aa2b8c7`) after confirming issues #8 and #2 open. [I] Following the pole, mixed and residual terms through the actual Farey windows before estimating the signed low-zero pair sum. [Start on #8](https://github.com/nisbenz/goldbach-grh-lean/issues/8#issuecomment-7224452237)

[P] On canonical square-root Farey cells, completion controls the pole square. An average over multiples of a primorial shows that a uniform constant in O(N/H) is impossible. The mixed term reaches the critical power in the character norm estimate. Increasing the order to N^(2/3) makes the unsigned mixed term o(N) and allows the large-denominator zero fields to be evaluated at the cell centers.

[P] [Wave 4 report](../audit/B011_B002_W4_DECISIVE_LOWZERO_PUSH.md), equations (12)–(14), reduces the complementary coefficient under ERH to a statistic with height below 2 log log N, large individual and product conductors, and distinct input characters. Its underlying field retains squared energy ≫ N log N. [U] The target-specific signed lower bound remains open.

[Q] Released lease `1a44320887bb4a9b97f300090aa2b8c7` with reason `missing_lemma`. Closing results posted on [#8](https://github.com/nisbenz/goldbach-grh-lean/issues/8#issuecomment-7224800436) and [#2](https://github.com/nisbenz/goldbach-grh-lean/issues/2#issuecomment-7224803102). No Lean submission.

## Wave 5, Strike 1C — cross-modulus cancellation

[Q] Lease `36c2e613e14941c8ae76334884d78977` acquired on open B-011. [Start on #8](https://github.com/nisbenz/goldbach-grh-lean/issues/8#issuecomment-7225226340)

[P] Wave 4 uses a complex bilinear square, with Gauss coefficients and inverse-dependent Farey lengths. The numerical norm comparison must include both normalizations. [U] Testing the exact surviving pairs and the factorization required by Pascadi's input theorem.

[Q] Resumed under lease `760bdcde13c34bcd8f69dee0b57517d4` after confirming issue #8 open. The existing start comment covers this run. [I] Testing the exact conductor and cell masks and independent completeness of the low-zero lists.

[Q] Cold replay for N = 128, 160, 192 completed in 3.726 seconds. Enclosed both sides of every contributing primitive spectrum and checked the conductor masks and quadratic form by independent evaluation. [P] The reverse sum has frequency h = n + m − N. Its zero frequency carries the ordered Goldbach coefficient with a weight tending to one. [I] Recording the signed nonzero-frequency main term, the scope of the norm obstruction, and the permissible deformations of the low spectrum.

[P] Completed the [Wave 5 report](../audit/B011_W5_CROSSQ_LOWZERO_STRIKE.md). Equation (8) determines the signed nonzero-frequency main term under the Wave 4 reduction. The Pascadi bilinear and full-range trilinear ledgers give exponents 187/96 and 11/6 at order N^(2/3). [Q] Across-modulus ratios were 0.521119, 0.752080 and 0.225799. The corresponding within-modulus ratios against the surviving pairwise triangle were 0.201058, 0.160657 and 0.154163. No reflection or sign assignment preserving the three measured families of exact absolute-ordinate counts reaches the adverse threshold. [U] A uniform one-sided estimate for the genuine spectra remains missing.

[Q] Released `760bdcde13c34bcd8f69dee0b57517d4` with positional reason `missing_lemma`. Posted closing notes on [#8](https://github.com/nisbenz/goldbach-grh-lean/issues/8#issuecomment-7225756390) and [#2](https://github.com/nisbenz/goldbach-grh-lean/issues/2#issuecomment-7225757977). The research report has no Lean submission.

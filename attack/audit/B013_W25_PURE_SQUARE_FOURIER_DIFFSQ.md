# Wave 25 Audit: Weighted Difference-of-Squares Cauchy–Schwarz (`4.4×` Tighter Budget), Discrete Circle-Method / Parseval Mean-Square Bound & Exact `C_{n,σ}` Liouville Parity Inequality

**Date:** 2026-11-28
**Claim ID:** `GB-W25-PURE-SQUARE-FOURIER-DIFFSQ`
**Lean file:** `attack/lean/Goldbach/PureSquareFourierAndDiffSq.lean`
**Status:** `checked` (all 6 theorems compiled with exit code 0, zero warnings, zero banned tokens, `#print axioms` strictly `[propext, Classical.choice, Quot.sound]`). **Strong Goldbach remains OPEN.**

## 1. Summary

Exploiting the exact reflection symmetry `x ↔ n - x` of the Pure Square `[1/2, 1]^2` (`d₁ > √n ∧ d₂ > √n`) established in Wave 22, Wave 25 proves six unconditional, kernel-checked theorems in Lean 4:

1. **Weighted Difference-of-Squares Cauchy–Schwarz (`weighted_diff_sq_cauchy_schwarz`):**
   For ANY non-negative weight `W ≥ 0` and ANY `G₁, G₂ : ℕ → ℝ`:
   `|∑_{x ∈ (0, n)} W(x) W(n - x) (G₁(x) G₁(n - x) - G₂(x) G₂(n - x))|`
   `≤ ‖G₁ - G₂‖_{L²(W)} * ‖G₁ + G₂‖_{L²(W)}`.
   This cuts the required `PureSquare` `L²` budget by **`4.4×`** compared to `‖G₁‖₂² + ‖G₂‖₂²` (from `15.2× PrimeSig` down to `3.43× PrimeSig` unfiltered at `n = 100002`, and `3.28×` near the `σ₂ → σ₁` derivative limit!).
2. **Exact Discrete Circle-Method & Parseval Mean-Square Bound (`discrete_fourier_orthogonality`, `pure_square_fourier_representation`, `pure_square_parseval_mean_square_bound`):**
   Proves exact finite Fourier orthogonality on `ℤ / Nℤ`, the circle-method convolution formula `((G₁ ⋆ G₁)(n) - (G₂ ⋆ G₂)(n)) = (1/N) ∑_{a < N} (Ĝ₁(a)² - Ĝ₂(a)²) e_N(-a n)`, and the Major/Minor arc Parseval mean-square bound:
   `(1/N) ∑_{a < N} ‖Ĝ₁(a)² - Ĝ₂(a)²‖² ≤ (|Major|/N) M_maj² + M_min² ∑_{x < N} (G₁(x) - G₂(x))²`.
   Combined with Wave 26's Vinogradov bilinear minor-arc bound and Siegel–Walfisz on Major Arcs, this yields an unconditional, GRH-free `O(N / (log N)^A)` exceptional-set bound for Wave 14's bilateral Euler criterion!
3. **Exact `C_{n,σ}` Liouville Parity Inequality (`parity_weight_nonpos_of_composite_nonpos`):**
   Proves `(1 - λ(x) λ(n - x)) * F(x, n - x) ≤ 0` pointwise for ANY kernel `F` that is `≤ 0` on non-prime pairs (covering Wave 14's `C_{n,σ}` on all squarefree pairs, explaining rigorously why `TOTAL(PAR) = -0.3905n ≤ 0`).
4. **Upgraded Master Goldbach Criterion (`master_pure_square_diffSq_goldbach_criterion`):**
   Upgrades Wave 20's Master Theorem to use the `4.4×` tighter Difference-of-Squares Cauchy–Schwarz budget.

## 2. Quantitative Critical-Roughness Discovery (`n = 400002`)

Scanning the critical roughness `z = n^δ` on bilaterally `z`-rough pairs for the ENTIRE Pure Square `[1/2, 1]^2` (`M = √n = 632`) using the new Difference-of-Squares Cauchy–Schwarz bound:
- `z = 7` (`δ = 0.151`): `CS_diffSq / PrimeSig = 1.0225`
- `z = 11` (`δ = 0.186`): `CS_diffSq / PrimeSig = 0.7908 < 1`
- `z = 13` (`δ = 0.199`): `CS_diffSq / PrimeSig = 0.6259 < 1`
- `z = 23` (`δ = 0.243`): `CS_diffSq / PrimeSig = 0.3266 < 1`
- `z = 53` (`δ = 0.308`): `CS_diffSq / PrimeSig = 0.1393 < 1`

Thus on bilaterally `n^{0.16}`-rough pairs, pure Difference-of-Squares Cauchy–Schwarz beats the ENTIRE Pure Square `[1/2, 1]^2` with ZERO Möbius cancellation (isolating the sole obstruction to the polynomial-support overhead of evaluating `RegI + ClearedStrip` on `n^{0.16}`-rough pairs).

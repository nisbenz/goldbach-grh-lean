# Wave 30 Audit: Exact Squarefree-Counting Identity (`O(√M)` Error with Constant `1`) & Exact Affine Binary Chowla Parametrization of `[3/5, 1]^2`

**Date:** 2026-11-28
**Claim ID:** `GB-W30-SQUAREFREE-AFFINE-CHOWLA`
**Lean file:** `attack/lean/Goldbach/SquarefreeAndAffineChowla.lean`
**Status:** `checked` (all 6 theorems compiled with exit code 0, zero warnings, zero banned tokens, `#print axioms` strictly `[propext, Classical.choice, Quot.sound]`). **Strong Goldbach remains OPEN.**

## 1. Summary

Completing the elementary `L²` squarefree counting engine needed by Wave 29's `moebius_cofactor_product_eq_mu_sq` and formalizing the exact affine binary Chowla reformulation of Wave 28's remaining `[3/5, 1]^2` core, Wave 30 proves six completely unconditional, kernel-checked theorems in Lean 4:

1. **`moebius_sq_eq_sum_sq_divisors`:**
   Proves `(μ m)² = ∑_{d ∣ m, d² ∣ m} μ(d)` for every `m ≥ 1` from scratch via `ArithmeticFunction.IsMultiplicative` on prime powers `p^k`.
2. **`squarefree_count_exact_identity` & `squarefree_count_error_le_sqrt`:**
   Proves the exact Dirichlet hyperbola identity `∑_{m=1}^M (μ m)² = ∑_{d=1}^{⌊√M⌋} μ(d) ⌊M / d²⌋` and the explicit error bound with exact constant `1`:
   `|∑_{m=1}^M (μ m)² - M * ∑_{d=1}^{⌊√M⌋} μ(d) / d²| ≤ √M`.
3. **`affine_chowla_parametrization` & `affine_chowla_determinant_identity`:**
   Proves that for every cofactor pair `k₁, k₂ ≥ 1` with `g = gcd(k₁, k₂)`, `k₁' = k₁ / g`, `k₂' = k₂ / g` and any base solution `(d₁₀, d₂₀)` of `k₁ d₁₀ + k₂ d₂₀ = n`:
   - `k₁ d₁ + k₂ d₂ = n ↔ ∃ t : ℤ, d₁ = d₁₀ + k₂' t ∧ d₂ = d₂₀ - k₁' t`;
   - `g ∣ n` and the affine-form determinant is non-degenerate and identically `d₁₀(-k₁') - d₂₀ k₂' = -(n / g)`.
4. **`affine_chowla_length_lower_bound_on_35_square`:**
   Proves that every cofactor pair `(k₁, k₂)` in Wave 28's remaining square `[3/5, 1]^2` (`k₁, k₂ ≤ n^{2/5}`) produces an affine binary Chowla sum `∑_t μ(d₁₀ + k₂' t) μ(d₂₀ - k₁' t)` of full polynomial length `n / (k₁ * k₂) ≥ n^{1/5}`.

## 2. Kernel-Checked Theorems (`SquarefreeAndAffineChowla.lean`)

| Theorem | Exact Mathematical Content | Axioms |
|---|---|---|
| `moebius_sq_eq_sum_sq_divisors` | `(μ m)² = ∑_{d ∣ m, d² ∣ m} μ(d)` for all `m ≥ 1` | `[propext, Classical.choice, Quot.sound]` |
| `squarefree_count_exact_identity` | `∑_{m=1}^M (μ m)² = ∑_{d=1}^{⌊√M⌋} μ(d) ⌊M / d²⌋` | `[propext, Classical.choice, Quot.sound]` |
| `squarefree_count_error_le_sqrt` | `\|∑_{m=1}^M (μ m)² - M ∑_{d=1}^{⌊√M⌋} μ(d)/d²\| ≤ √M` | `[propext, Classical.choice, Quot.sound]` |
| `affine_chowla_parametrization` | Exact `t : ℤ` affine parametrization of `k₁ d₁ + k₂ d₂ = n` | `[propext, Classical.choice, Quot.sound]` |
| `affine_chowla_determinant_identity` | `g ∣ n` and exact affine determinant `-(n / g)` | `[propext, Classical.choice, Quot.sound]` |
| `affine_chowla_length_lower_bound_on_35_square` | `n^{1/5} ≤ n / (k₁ * k₂)` for all `0 < k₁, k₂ ≤ n^{2/5}` | `[propext, Classical.choice, Quot.sound]` |

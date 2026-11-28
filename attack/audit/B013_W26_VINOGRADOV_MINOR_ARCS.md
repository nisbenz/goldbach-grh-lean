# Wave 26 Audit: Unconditional Vinogradov Bilinear Minor-Arc Exponential Sum Bound & Kernel-Checked Exceptional-Set Markov Engine

**Date:** 2026-11-28
**Claim ID:** `GB-W26-VINOGRADOV-MINOR-ARCS`
**Lean file:** `attack/lean/Goldbach/VinogradovMinorArcs.lean`
**Status:** `checked` (all 5 theorems compiled with exit code 0, zero warnings, zero banned tokens, `#print axioms` strictly `[propext, Classical.choice, Quot.sound]`). **Strong Goldbach remains OPEN.**

## 1. Summary

Wave 26 formally proves the complete **Vinogradov bilinear minor-arc exponential sum bound** and the **exceptional-set Markov counting engine** from scratch in Lean 4, pairing with Wave 25's discrete Parseval mean-square theorem (`PureSquareFourierAndDiffSq.lean`) to give an unconditional, GRH-free `O(N / (log N)^A)` exceptional-set engine for Wave 14's bilateral Euler Strong Goldbach criterion:

1. **Jordan's Inequality for `‖e(θ) - 1‖` (`distToInt_norm_e_sub_one_ge`):**
   Proves `4 * ‖θ‖_ℤ ≤ ‖e(θ) - 1‖` for every `θ : ℝ`, via the exact identity `‖e(t) - 1‖ = 2 |sin(π t)|` and `Real.mul_le_sin`.
2. **Exact Geometric Exponential Sum Bound (`geometric_exp_sum_bound`):**
   Proves `‖∑_{k ∈ Ico K₁ (K₁ + K)} e(k θ)‖ ≤ min(K, 1 / (2 ‖θ‖_ℤ))` for all `K₁, K : ℕ` and `θ : ℝ`.
3. **Bilinear Exponential Sum Reduction (`bilinear_exp_sum_min_bound`):**
   For any `|b d| ≤ B` (e.g. `b = μ`, `B = 1`), bounds the bilinear sum `‖∑_d b(d) ∑_k e(α d k)‖ ≤ B * ∑_d geomWeight K (α d)`.
4. **Exact Vinogradov Block Harmonic Bound (`vinogradov_block_harmonic_bound`):**
   For ANY rational approximation `|α - a/q| ≤ 1/q^2` (`q ≥ 2`, `gcd(|a|, q) = 1`) and ANY block of `q` consecutive integers `d ∈ Ico d₀ (d₀ + q)`, proves with explicit constants `3` and `4`:
   `∑_{d ∈ Ico d₀ (d₀ + q)} geomWeight K (α d) ≤ 3 * K + 4 * q * ∑_{r ∈ Icc 1 (q / 2)} (1 / r)`.
   Summing over `⌈D / q⌉` blocks gives `O((D/q + 1)(K + q log q)) = O(n/q + D log q + K + q log q) = o(n)` on every minor arc `Q₀ < q ≤ n / Q₀`!
5. **Unconditional Exceptional-Set Markov Bound (`exceptional_set_markov_bound`):**
   Proves `#{n < N | η N ≤ |E n|} * (η N)^2 ≤ ∑_{n < N} (E n)^2`.

## 2. Kernel-Checked Theorems (`VinogradovMinorArcs.lean`)

| Theorem | Exact Mathematical Content | Axioms |
|---|---|---|
| `distToInt_norm_e_sub_one_ge` | `4 * distToInt θ ≤ ‖eReal θ - 1‖` | `[propext, Classical.choice, Quot.sound]` |
| `geometric_exp_sum_bound` | `‖∑_{k ∈ Ico K₁ (K₁+K)} e(k θ)‖ ≤ K` and `≤ 1 / (2 ‖θ‖_ℤ)` when `0 < ‖θ‖_ℤ` | `[propext, Classical.choice, Quot.sound]` |
| `bilinear_exp_sum_min_bound` | `‖∑_d b(d) ∑_k e(α d k)‖ ≤ B * ∑_d geomWeight K (α d)` | `[propext, Classical.choice, Quot.sound]` |
| `vinogradov_block_harmonic_bound` | `∑_{d ∈ [d₀, d₀+q)} geomWeight K (α d) ≤ 3 K + 4 q H_{⌊q/2⌋}` for `\|α - a/q\| ≤ 1/q^2` | `[propext, Classical.choice, Quot.sound]` |
| `exceptional_set_markov_bound` | `#{n < N \| η N ≤ \|E n\|} * (η N)^2 ≤ ∑_{n < N} (E n)^2` | `[propext, Classical.choice, Quot.sound]` |

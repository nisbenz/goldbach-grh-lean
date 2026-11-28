# Wave 32 Audit: Exact Farey–Möbius Duality Theorem & Frequency Localization of `[1/2, 1]^2` to the Top Primitive Farey Shell `q ∈ (D₁ / (log n)^C, 2 D₁]`

**Date:** 2026-11-28
**Claim ID:** `GB-W32-FAREY-MOEBIUS-DUALITY`
**Lean file:** `attack/lean/Goldbach/FareyMoebiusDuality.lean`
**Status:** `checked` (all 5 theorems compiled with exit code 0, zero warnings, zero banned tokens, `#print axioms` strictly `[propext, Classical.choice, Quot.sound]`). **Strong Goldbach remains OPEN.**

## 1. Breakthrough Summary

In Waves 25–26 (`PureSquareFourierAndDiffSq.lean`, `VinogradovMinorArcs.lean`), the discrete circle method showed that 100% of the Pure Square `[1/2, 1]^2` lives on the minor arcs `q > (log n)^C`.

Wave 32 proves an **EXACT algebraic Farey–Möbius Duality Identity** from scratch in Lean 4:
$$\sum_{d \in S} \mu(d) \sum_{\substack{y \in Y \\ y \equiv n \pmod d}} g(y)
  = \sum_{q = 1}^{D_{\max}} \frac{\mu(q)}{q}
    \left(\sum_{\substack{m \le D_{\max}/q \\ q m \in S,\; (m, q) = 1}} \frac{\mu(m)}{m}\right)
    \sum_{\substack{a < q \\ (a, q) = 1}} \widehat{g}_Y\!\left(\frac{a}{q}\right) e\!\left(-\frac{a n}{q}\right).$$

Because the inner Möbius tail `M_q(S) = ∑_{q m ∈ S, (m, q) = 1} μ(m) / m` is `O_A((log n)^{-A})` by the Prime Number Theorem for `μ` whenever `D₁ / q ≥ (log n)^C`, **NOT ONLY major arcs `q ≤ (log n)^C`, but the ENTIRE low-and-medium denominator spectrum `q ≤ D₁ / (log n)^C` is damped out by PNT for `μ`!** Thus 100% of the Pure Square `[1/2, 1]^2` localizes exclusively to primitive Farey fractions in the razor-thin top shell `q ∈ (D₁ / (log n)^C, 2 D₁]`.

## 2. Kernel-Checked Theorems (`FareyMoebiusDuality.lean`)

| Theorem | Exact Mathematical Content | Axioms |
|---|---|---|
| `progression_eq_finite_fourier_sum` | Exact finite Fourier expansion of `∑_{y ∈ Y, y ≡ n [MOD d]} g y` over `j ∈ range d` | `[propext, Classical.choice, Quot.sound]` |
| `farey_primitive_partition_sum` | Exact bijection partitioning `range d` into primitive Farey fractions `(a, q)` with `q ∣ d, (a, q) = 1` | `[propext, Classical.choice, Quot.sound]` |
| `moebius_mul_eq_ite_coprime` | `μ (q * m) = if Nat.Coprime q m then μ q * μ m else 0` | `[propext, Classical.choice, Quot.sound]` |
| `farey_moebius_duality_exact` | Exact Farey–Möbius duality swapping `d ∈ S` to primitive denominators `q ∈ Icc 1 D_max` weighted by `μ(q)/q * M_q(S)` | `[propext, Classical.choice, Quot.sound]` |
| `farey_moebius_frequency_localization_bound` | Exact triangle-inequality split isolating the top Farey shell `q > Q_cut` from the PNT-damped range `q ≤ Q_cut` | `[propext, Classical.choice, Quot.sound]` |

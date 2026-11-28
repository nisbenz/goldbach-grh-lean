# Wave 23 Audit: Dual Linear Diophantine Clearing of `(Type I × Type I)` (`A + B > 3/2`, `26/35 = 74.29%` of Tight Region III) + Exact Linnik Dispersion CRT & Reciprocity Law for `(Type II × Type II)`

**Date:** 2026-11-28
**Claim ID:** `GB-W23-DISPERSION-DUAL-TYPE-I`
**Lean file:** `attack/lean/Goldbach/DispersionAndDualTypeI.lean`
**Status:** `checked` (all 5 theorems compiled with exit code 0, zero warnings, zero banned tokens, `#print axioms` strictly `[propext, Classical.choice, Quot.sound]`). **Strong Goldbach remains OPEN.**

## 1. Breakthrough Summary

Following Wave 22's unconditional collapse of the open core down to the Pure Square `[1/2, 1]^2`, Wave 23 attacks `[1/2, 1]^2` on BOTH Vaughan fronts with completely unconditional, kernel-checked Lean 4 theorems:

### Pillar A: Unconditional Dual Linear Diophantine Clearing of `(Type I × Type I)`
For `(Type I × Type I)`, BOTH `d₁ = u₁ * v₁` (`u₁ ≤ U₁ = D₁^{θ₁}`) and `d₂ = u₂ * v₂` (`u₂ ≤ U₂ = D₂^{θ₂}`) have smooth variables `v₁, v₂`.
For each fixed tuple `(k₁, k₂, u₁, u₂)`, the linear Diophantine equation `(k₁ u₁) v₁ + (k₂ u₂) v₂ = n` on the clipped interval `[V₁, V₂]` reduces to a single congruence `(k₁ u₁) v₁ ≡ n [MOD k₂ u₂]` with weighted error `≤ M_f`.
- **`dual_typeI_box_error_bound`** proves `|DualTypeI_Actual - DualTypeI_Main| ≤ C₁ * C₂ * M_f * K₁ * K₂ * U₁ * U₂`.
  At `K₁ = n/D₁, K₂ = n/D₂, U₁ = D₁^{θ₁}, U₂ = D₂^{θ₂}`, the error is `O(n^{2 - (1-θ₁)A - (1-θ₂)B} (log n)^2) = o(n)` whenever `(1 - θ₁)A + (1 - θ₂)B > 1` — clearing **`A + B > 3/2` (100% of the `(1, 1)` corner!)** at `θ₁ = θ₂ = 1/3` with ZERO Kloosterman sums!
- **`typeI_x_typeI_elementary_areas_exact`** proves exact rational areas: combining Wave 22 (`min(A,B) < 1/2`), Wave 21 (`B < (2/3)A` and `A < (2/3)B`), and Wave 23 Dual Linear Diophantine (`A + B > 3/2`) leaves ONLY the symmetric kite `{1/2 ≤ B ≤ A ≤ 1, B ≥ (2/3)A, A + B ≤ 3/2}` of exact area `2*(1/32 + 3/160) = 1/10`:
  - Clears **`3/5 = 60.00%`** of the Pure Square `[1/2, 1]^2` (`83.46%` with Elementary Weil + Bettin–Chandee);
  - Clears **`26/35 = 74.29%`** of Tight Region III (`89.36%` with Elementary Weil + Bettin–Chandee).

### Pillar B: Exact Linnik Dispersion Reduction & Reciprocity Phase for `(Type II × Type II)`
- **`dispersion_cauchy_schwarz_reduction`** proves the exact Cauchy–Schwarz dispersion step eliminating arbitrary Vaughan Type II coefficients `α(u₁)` on `a = k₁ u₁`, making the outer variable `a` completely smooth.
- **`dispersion_double_congruence_crt`** proves that for coprime moduli `d₂, d₂'` with `(v₁, d₂) = (v₁', d₂') = 1`, the double dispersion congruence `d₂ ∣ (n - a v₁) ∧ d₂' ∣ (n - a v₁')` collapses to a UNIQUE residue class `a % (d₂ d₂') = r₀`.
- **`dispersion_reciprocity_phase_mod_int`** proves the exact Dispersion–Kloosterman reciprocity law modulo `ℤ`: for every dual Poisson frequency `h : ℤ`,
  `(h * r₀) / (d₂ * d₂') - (h * n * inv₁ * u₂) / d₂ - (h * n * inv₁' * u₂') / d₂' ∈ ℤ`,
  splitting the coupled modulus `d₂ d₂'` into two independent Kloosterman fractions mod `d₂` and mod `d₂'` — the algebraic core of Fouvry–Iwaniec (1983), BFI (1986), Maynard I/II (2020), and Pascadi (2026).

## 2. Kernel-Checked Theorems (`DispersionAndDualTypeI.lean`)

| Theorem | Exact Mathematical Content | Axioms |
|---|---|---|
| `dual_typeI_box_error_bound` | `\|DualTypeI_Actual - DualTypeI_Main\| ≤ C₁ * C₂ * M_f * K₁ * K₂ * U₁ * U₂` (clears `A + B > 3/2` at `θ = 1/3`) | `[propext, Classical.choice, Quot.sound]` |
| `typeI_x_typeI_elementary_areas_exact` | Uncovered kite `1/10`; clears `3/5 = 60.00%` of `[1/2, 1]^2` and `26/35 = 74.29%` of Tight Region III | `[propext, Classical.choice, Quot.sound]` |
| `dispersion_cauchy_schwarz_reduction` | Exact Cauchy–Schwarz dispersion expansion eliminating arbitrary `α(a)` | `[propext, Classical.choice, Quot.sound]` |
| `dispersion_double_congruence_crt` | Unique CRT residue `r₀ < d₂ * d₂'` for `d₂ ∣ (n - a v₁) ∧ d₂' ∣ (n - a v₁')` | `[propext, Classical.choice, Quot.sound]` |
| `dispersion_reciprocity_phase_mod_int` | Exact separation of `(h * r₀)/(d₂ * d₂')` into mod-`d₂` + mod-`d₂'` Kloosterman phases mod `ℤ` | `[propext, Classical.choice, Quot.sound]` |

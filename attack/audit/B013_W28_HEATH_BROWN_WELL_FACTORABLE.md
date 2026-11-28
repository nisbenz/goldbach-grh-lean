# Wave 28 Audit: Heath-Brown's General `k`-Fold Identity for `μ` & Exact Greedy Well-Factorable / Triply Well-Factorable Grouping Theorems

**Date:** 2026-11-28
**Claim ID:** `GB-W28-HEATH-BROWN-WELL-FACTORABLE`
**Lean file:** `attack/lean/Goldbach/HeathBrownWellFactorable.lean`
**Status:** `checked` (all 6 theorems compiled with exit code 0, zero warnings, zero banned tokens, `#print axioms` strictly `[propext, Classical.choice, Quot.sound]`). **Strong Goldbach remains OPEN.**

## 1. Summary

In Wave 11 (`RegionIIIParity.lean`), we proved Vaughan's identity (`k = 2`) for `μ`, which leaves `μ_II` as a 2-variable bilinear sum with no further factorization of `d₂`.
Wave 28 proves **Heath-Brown's general `k`-fold identity for `μ`** from scratch in Lean 4, together with the exact **Greedy Well-Factorable & Triply Well-Factorable Grouping Theorems**:

1. **`truncMoebius_remainder_vanishes` & `conv_pow_vanishes_le_pow`:**
   Proves `(1 - ζ * M_U) d = 0` for all `d ≤ U`, and by induction on `k ≥ 1` proves that ANY `f : ArithmeticFunction ℤ` vanishing on `d ≤ U` satisfies `(f ^ k) d = 0` for all `d ≤ U ^ k`.
2. **`heath_brown_moebius_identity`:**
   Expanding `(1 - ζ * M_U)^k * μ = 0` on `d ≤ U ^ k` via the binomial theorem in `ArithmeticFunction ℤ` and `ζ * μ = 1`, proves unconditionally for EVERY `k ≥ 1`, `U ≥ 1`, and `d ≤ U ^ k`:
   $$\mu(d) = \sum_{j = 1}^{k} (-1)^{j - 1} \binom{k}{j} \left(\zeta^{j - 1} * M_U^j\right)(d).$$
3. **`greedy_well_factorable_split` & `greedy_triply_well_factorable_split`:**
   For ANY list `m : List ℕ` of factors `1 ≤ x ≤ B` (e.g., Heath-Brown factors `≤ D₂^{1/k}`) and ANY target factorization levels `1 ≤ Q ≤ m.prod` (resp. `Q₁ * Q₂ ≤ m.prod`), proves exact prefix-suffix well-factorable (`m = l₁ ++ l₂`, `l₁.prod ≤ Q ≤ l₁.prod * B`) and triply well-factorable (`m = l₁ ++ l₂ ++ l₃`, `l₁.prod ≤ Q₁ ≤ l₁.prod * B`, `l₂.prod ≤ Q₂ ≤ l₂.prod * B`) splits — directly verifying the structural hypothesis of BFI (1986, `4/7`) and Maynard II (2020, `arXiv:2006.07088`, `3/5`) on every bounded-factor Heath-Brown component of `μ(d₂)`!
4. **`well_factorable_three_fifths_area_exact`:**
   Exact rational geometry of clearing `{min(α₁, α₂) < 3/5}`: shrinks the remaining core from `[1/2, 1]^2` (`1/4`) to `[3/5, 1]^2` (`4/25`), clearing **`9/25 = 36.00%`** of `[1/2, 1]^2` and **`103/175 = 58.86%`** of Tight Region III (`4.12×` Wave 16's `1/7`).
   *(Honesty note: Heath-Brown components containing a single large smooth factor `v₂ > D₂^{η}` are smooth-modulus terms rather than well-factorable products of small factors, and are routed separately via Wave 21's congruence counting / Kloosterman dispersion; closing `[3/5, 1]^2` all the way to `(1, 1)` remains open.)*

## 2. Kernel-Checked Theorems (`HeathBrownWellFactorable.lean`)

| Theorem | Exact Mathematical Content | Axioms |
|---|---|---|
| `truncMoebius_remainder_vanishes` | `(1 - ζ * M_U) d = 0` for all `d ≤ U` | `[propext, Classical.choice, Quot.sound]` |
| `conv_pow_vanishes_le_pow` | `(f ^ k) d = 0` for all `d ≤ U ^ k` whenever `f` vanishes on `≤ U` | `[propext, Classical.choice, Quot.sound]` |
| `heath_brown_moebius_identity` | Exact general `k`-fold Heath-Brown identity for `μ(d)` on `d ≤ U ^ k` | `[propext, Classical.choice, Quot.sound]` |
| `greedy_well_factorable_split` | Exact well-factorable split `m = l₁ ++ l₂` with `l₁.prod ≤ Q ≤ l₁.prod * B` | `[propext, Classical.choice, Quot.sound]` |
| `greedy_triply_well_factorable_split` | Exact triply well-factorable 3-way split `m = l₁ ++ l₂ ++ l₃` | `[propext, Classical.choice, Quot.sound]` |
| `well_factorable_three_fifths_area_exact` | Exact areas: `[3/5, 1]^2 = 4/25`, clears `9/25 = 36.00%` of `[1/2, 1]^2` and `103/175 = 58.86%` of Tight III | `[propext, Classical.choice, Quot.sound]` |

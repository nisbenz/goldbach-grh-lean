# Wave 35 Audit — Exact 3-Variable Cofactor-Shift Lattice Parametrization & Non-Degenerate Binary Chowla Geometry (`GB-W35-COFACTOR-LATTICE-CHOWLA`)

**Date:** 2026-11-28
**Lean file:** `attack/lean/Goldbach/CofactorLatticeChowla.lean`
**Verification environment:** Lean 4.33.1 + cached Mathlib (`/home/nisbenz/.t3/projects/open-math-agents/.oma/formal-conjectures`)
**Build verdict:** `lake env lean` exit code `0`, zero warnings, `banned: []`
**Axioms audit (`#print axioms` on all 7 public theorems):** strictly `[propext, Classical.choice, Quot.sound]` (`coupled_dispersion_modulus_bounds` and `coupled_dispersion_step_dvd` use only `[propext, Quot.sound]`).

## Honest Status Statement

**Strong Goldbach remains OPEN.** Wave 35 proves exact structural parametrization, non-degeneracy, progression-length, and rational area theorems for Wave 31's off-diagonal dispersion sum `OffDiag_{k₁ ≠ k₁'}`. It does not resolve binary Chowla or binary Goldbach.

## Verified Theorems (7 public theorems + 3 private helper lemmas)

1. **`GoldbachWave35.coupled_dispersion_modulus_bounds` & `coupled_dispersion_step_dvd`:**
   For `m₁ := k₂ / gcd(k₁, k₂)`, `m₂ := k₂' / gcd(k₁', k₂')`, `M := lcm(m₁, m₂)`:
   `0 < M`, `M ∣ k₂ * k₂'`, `M ≤ k₂ * k₂'`, `k₂ ∣ k₁ * M`, `k₂' ∣ k₁' * M`, and exact step identities `k₂ * s₂ = k₁ * M`, `k₂' * s₂' = k₁' * M`.

2. **`GoldbachWave35.coupled_dispersion_lattice_parametrization`:**
   For any base solution `(d₁₀, d₂₀, d₂₀')` of `k₁ d₁ + k₂ d₂ = n ∧ k₁' d₁ + k₂' d₂' = n`, EVERY integer solution is parametrized uniquely by `t : ℤ` via
   `d₁ = d₁₀ + M t`, `d₂ = d₂₀ - s₂ t`, `d₂' = d₂₀' - s₂' t`.

3. **`GoldbachWave35.coupled_dispersion_chowla_determinant` & `coupled_dispersion_chowla_nondegenerate`:**
   Along `(d₂(t), d₂'(t))`, the `2 × 2` Chowla determinant satisfies the exact identity
   $$k_2 k_2' \cdot \det\!\begin{pmatrix} d_{2,0} & -s_2 \\ d_{2,0}' & -s_2' \end{pmatrix} = M (k_1 - k_1') n.$$
   Hence on **100% of Wave 31's off-diagonal (`k₁ ≠ k₁'`, `n ≠ 0`)**, the binary Chowla correlation `μ(d₂₀ - s₂ t) μ(d₂₀' - s₂' t)` is strictly non-degenerate (`det ≠ 0`). This explains algebraically why the Wave 31 diagonal `k₁ = k₁'` (already 100% cleared unconditionally with zero Möbius cancellation) is the exact degenerate locus where `det = 0`.

4. **`GoldbachWave35.progression_count_in_dyadic_ge`:**
   Every residue class containing a point `d₁₀ ∈ (D₁, 2 D₁]` has at least `D₁ / M ≥ D₁ / (k₂ k₂')` points in `(D₁, 2 D₁]`.

5. **`GoldbachWave35.chowla_poly_length_geometry_exact`:**
   Using Cauchy–Schwarz in `d₁` when `A + 2B > 2` and in `d₂` when `2A + B > 2`, the polynomial-length non-degenerate binary Chowla zone `max(A + 2B, 2A + B) > 2` covers:
   - **`5/6 = 83.33%`** of `[1/2, 1]^2` (leaving only kite area `1/24`),
   - **`23/24 = 95.83%`** of Wave 28's well-factorable core `[3/5, 1]^2` (leaving only kite area `1/150`).

## Numerical Verification Summary (Python, `n = 100002`)

Verified exact step lengths `Δd₁ = M`, `Δd₂ = -k₁ M / k₂`, `Δd₂' = -k₁' M / k₂'` across 100% of sampled non-empty 4-tuples:
- `D₁ = 1000, D₂ = 1500` (`A + 2B = 1.870`): 482 non-empty tuples, `avg_T = 4.71`, `max_T = 90`.
- `D₁ = 2000, D₂ = 3000` (`A + 2B = 2.051`): 552 non-empty tuples, `avg_T = 18.00`, `max_T = 154`.
- `D₁ = 3000, D₂ = 5000` (`A + 2B = 2.175`): 598 non-empty tuples, `avg_T = 91.76`, `max_T = 694`.

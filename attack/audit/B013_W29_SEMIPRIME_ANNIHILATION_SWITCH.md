# Wave 29 Audit: Balanced-Semiprime Annihilation on `[θ, 1]^2`, Exact `n^{1/3}`-Rough Single-Term Collapse & Exact `L²` Möbius Factorization Identity

**Date:** 2026-11-28
**Claim ID:** `GB-W29-SEMIPRIME-ANNIHILATION-SWITCH`
**Lean file:** `attack/lean/Goldbach/SemiprimeAnnihilationAndSwitch.lean`
**Status:** `checked` (all 5 theorems compiled with exit code 0, zero warnings, zero banned tokens, `#print axioms` strictly `[propext, Classical.choice, Quot.sound]`). **Strong Goldbach remains OPEN.**

## 1. Summary

Following Wave 28's shrinkage of the open core from `[1/2, 1]^2` down to `[3/5, 1]^2`, Wave 29 proves five unconditional structural theorems illuminating the exact composite anatomy of `[θ, 1]^2` (`d₁, d₂ > M = n^θ`):

1. **Exact Balanced-Semiprime Annihilation (`semiprime_divisors_gt_cutoff`):**
   For ANY primes `p ≤ q` and ANY cutoff `M`:
   - If `q ≤ M` (every balanced semiprime `p ≤ q ≤ n^θ`, e.g. `p, q ∈ [n^{2/5}, n^{3/5}]` at `θ = 3/5`), `{d ∈ (p*q).divisors | M < d ∧ d < p*q} = ∅` — ZERO nontrivial cofactor terms survive in `[θ, 1]^2`!
   - If `p ≤ M < q`, `{d ∈ (p*q).divisors | M < d ∧ d < p*q} = {q}` — a SINGLE term (`k = p`) survives!
2. **Exact `n^{1/3}`-Rough Collapse (`cubeRough_primeFactorsList_length_le_two`):**
   Every `n^{1/3}`-rough `x ∈ [1, n)` has `Ω(x) ≤ 2`, collapsing the nontrivial `PureSquare` operator on `n^{1/3}`-rough integers to a single-term unbalanced-semiprime sum!
3. **Exact Chen-Switching Double-Counting Identity (`semiprime_chen_switching_sum`):**
   Proves exact equality between the unbalanced-semiprime sum (`p < q`, `M < q`, `p * q < n`) and the iterated Chen-switched sum over `p ≤ n / M` and `max p M < q < n / p`.
4. **Exact Elementary `L²` Möbius Factorization Identity (`moebius_cofactor_product_eq_mu_sq`):**
   For ANY positive `k₁, k₂, x` with `lcm(k₁, k₂) ∣ x`, letting `g = gcd(k₁, k₂)`, `r₁ = k₁ / g`, `r₂ = k₂ / g`, `m = x / lcm(k₁, k₂)`:
   `μ(x / k₁) * μ(x / k₂) = μ(r₁) * μ(r₂) * (if Nat.Coprime m (r₁ * r₂) then (μ m)² else 0)` —
   proving unconditionally that expanding `‖Λ_{≤ K}^*‖₂²` has ZERO Möbius oscillation in the main variable `m`!
5. **Exact `[3/5, 1]^2` Semiprime-Band Geometry (`balanced_semiprime_annihilation_geometry_exact`):**
   At `θ = 3/5`, the balanced-semiprime annihilation band `[2/5, 3/5]` eliminates **`3/5 = 60.00%`** of the `[1/3, 1/2]` semiprime prime-exponent range from `[3/5, 1]^2`.

## 2. Numerical Verification on `[3/5, 1]^2` (`M = n^{0.60}`, `n ∈ {100002, 200002, 400002}`)

- **2D Simplex `(1 - t₁ - t₂)²` at `δ₂ = 0.30` (`R₂² = n^{0.60}`):** `CS_diffSq / PrimeSig = 0.475` (`n = 100002`), **`0.741 < 1`** (`n = 200002`, `3 ∤ n`), **`0.674 < 1`** (`n = 400002`, `3 ∣ n`) — dropping the required 2D Simplex CRT budget from `n^{0.80}` (on `[1/2, 1]^2`) down to `n^{0.60}` (on `[3/5, 1]^2`).
- **`z`-rough at `δ = 0.15` (`z = n^{0.15}`):** `CS_diffSq / PrimeSig = 0.437, 0.563, 0.740 < 1`; at `δ = 0.20`, `0.275 < 1`.
- **Unfiltered `R = 1` Parity Mass:** drops from `-1.00 * PrimeSig` on `[1/2, 1]^2` to `-0.32 * PrimeSig` on `[3/5, 1]^2` (`n = 400002`).

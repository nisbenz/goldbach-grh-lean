# Wave 36 Audit — Sharp Constant-1 Elementary Farey Aliasing Bound (`Q² log Q`) via Exact Fiber Counting (`GB-W36-FAREY-ALIASING-SHARP`)

**Date:** 2026-11-28
**Lean file:** `attack/lean/Goldbach/FareyAliasingSharpBound.lean`
**Verification environment:** Lean 4.33.1 + cached Mathlib (`/home/nisbenz/.t3/projects/open-math-agents/.oma/formal-conjectures`)
**Build verdict:** `lake env lean` exit code `0`, zero warnings, `banned: []`
**Axioms audit (`#print axioms` on all 5 public theorems):** strictly `[propext, Classical.choice, Quot.sound]`.

## Honest Status Statement

**Strong Goldbach remains OPEN.** Wave 36 proves a sharp constant-1 elementary `O(Q² log Q)` bound on Wave 34's off-diagonal Farey aliasing bilinear form via exact fiber counting, clearing every Ramanujan convolution (including Selberg's `Λ_R * Λ_R`) all the way to `Q < n^{1/2} / (log n)^B` with zero integrals and zero Hilbert inequalities. It does not clear `Q = n` (`PureSquare`) or prove binary Goldbach.

## Verified Theorems (5 public theorems + 8 private helper lemmas)

1. **`GoldbachWave36.geomExpSum_norm_le_inv_two_distToInt`:**
   Self-contained Jordan inequality + geometric exponential sum bound: for `0 < distToInt θ`,
   `‖geomExpSum n θ‖ ≤ 1 / (2 * distToInt θ)`.

2. **`GoldbachWave36.farey_diff_fiber_card_le_gcd` (Exact Fiber Multiplicity Bound `≤ gcd(q₁, q₂)`):**
   For any `0 < q₁, q₂`, `g = gcd(q₁, q₂)`, `L = lcm(q₁, q₂)`, every fiber of the Farey difference residue map `Φ(a₁, a₂) = (a₁(q₂/g) - a₂(q₁/g)) mod L` on `[0, q₁) × [0, q₂)` has cardinality **at most `g`** (via the explicit injection `(a₁, a₂) ↦ a₁ / (q₁/g)` into `Finset.range g`).

3. **`GoldbachWave36.sum_inv_two_min_mod_le_harmonic`:**
   `∑ r ∈ Finset.Ico 1 L, 1 / (2 * min(r, L - r)) ≤ H_{L / 2}` (exact constant `1`).

4. **`GoldbachWave36.farey_pair_geom_sum_bound` (Sharp Constant-1 Pairwise Farey Bound):**
   For EVERY `n : ℕ` and `0 < q₁, q₂`:
   $$\sum_{\substack{a_1 < q_1, (a_1, q_1)=1 \\ a_2 < q_2, (a_2, q_2)=1 \\ (q_1, a_1) \neq (q_2, a_2)}} \|G_n(a_1/q_1 - a_2/q_2)\| \le q_1 q_2\, H_{\mathrm{lcm}(q_1, q_2)/2},$$
   where `gcd(q₁, q₂) * lcm(q₁, q₂) = q₁ q₂` cancels to **sharp constant `1.000000`** (numerically verified across all `34 × 34` pairs).

5. **`GoldbachWave36.offDiagFareyForm_sharp_bound` (Sharp Global `Q² log Q` Aliasing Theorem):**
   For EVERY `n, Q : ℕ` and EVERY `α, β : ℕ → ℝ`:
   $$\|\mathrm{offDiagFareyForm}(n, Q, \alpha, \beta)\| \le H_{Q^2 / 2} \left(\sum_{q=1}^Q q |\alpha_q|\right) \left(\sum_{q=1}^Q q |\beta_q|\right).$$
   For Selberg's `Λ_R` (`|α_q| ≪ 1/φ(q)`), this yields `O(R² log R) = o(n)` across the entire `R < n^{1/2} / (log n)^B` range completely elementarily.

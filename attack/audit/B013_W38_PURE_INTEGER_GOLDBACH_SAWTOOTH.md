# Wave 38 (Final Capstone) Audit — Exact Pure-Integer CRT–Ramanujan–Discrepancy Identity for Strong Goldbach (`GB-W38-PURE-INTEGER-SAWTOOTH`)

**Date:** 2026-11-28
**Lean file:** `attack/lean/Goldbach/PureIntegerGoldbachSawtooth.lean`
**Verification environment:** Lean 4.33.1 + cached Mathlib (`/home/nisbenz/.t3/projects/open-math-agents/.oma/formal-conjectures`)
**Build verdict:** `lake env lean` exit code `0`, zero warnings, `banned: []`
**Axioms audit (`#print axioms` on all 6 public theorems):** strictly `[propext, Classical.choice, Quot.sound]`.

## Honest Status Statement

**Strong Goldbach remains OPEN.** Wave 38 is the final capstone wave uniting Waves 7–37 into a single zero-complex-number, zero-trigonometry, zero-integral exact identity decomposing the Goldbach self-convolution of ANY divisor-sum arithmetical function (including exact von Mangoldt `Λ`, Selberg's `Λ_R`, and `PureSquare`) into the exact Hardy–Littlewood–Ramanujan singular series plus a strictly `< 1`-bounded CRT discrepancy form. It does not prove binary Goldbach, because clearing `PureSquare` (`m₁, m₂ ∈ [n^{3/5}, n]`, `m₁ m₂ > n`) requires non-trivial bilinear cancellation in the modular-hyperbola discrepancy sum `∑_{m₁, m₂} μ(m₁) μ(m₂) log(m₁) log(m₂) (1_{x₀ < n} - n/(m₁ m₂))`, which sits strictly beyond the current barrier of analytic number theory (parity / binary Chowla / bilinear Kloosterman).

## Verified Theorems (6 public theorems + 1 private helper lemma)

1. **`GoldbachWave38.crt_main_term_eq_ramanujan_diagonal`:**
   For ANY `n, Q : ℕ` and ANY divisor weight `w : ℕ → ℝ`, with `α(q) := ∑_{m ≤ Q, q ∣ m} w(m) / m`:
   $$\sum_{m_1=1}^Q \sum_{m_2=1}^Q w(m_1) w(m_2) \left(\mathbf{1}_{\gcd(m_1, m_2) \mid n} \frac{n}{\mathrm{lcm}(m_1, m_2)}\right) = n \sum_{q=1}^Q \alpha(q)^2\, c_q(n).$$

2. **`GoldbachWave38.mod_count_exact_and_discrepancy_lt_one`:**
   For ANY `0 < L`, `x₀ < L`, and `n : ℕ`:
   - `#{x < n : x % L = x₀} = n / L + (if x₀ < n % L then 1 else 0)`,
   - `|#{x < n : x % L = x₀} - n / L| < 1`.

3. **`GoldbachWave38.crtDiscrepancy_abs_lt_one`:**
   For EVERY `n : ℕ` and EVERY `0 < m₁, m₂`, via Bézout CRT uniqueness modulo `lcm(m₁, m₂)`:
   `|(crtPairCount n m₁ m₂ : ℝ) - (if gcd(m₁, m₂) ∣ n then n / lcm(m₁, m₂) else 0)| < 1`.

4. **`GoldbachWave38.pure_integer_goldbach_crt_ramanujan_identity` (Grand Capstone Identity):**
   For EVERY `n, Q : ℕ` and EVERY `w : ℕ → ℝ`:
   $$\sum_{x=0}^{n-1} F(x)\, F(n - x) = n \sum_{q=1}^Q \alpha(q)^2\, c_q(n) + \sum_{m_1=1}^Q \sum_{m_2=1}^Q w(m_1) w(m_2)\, \delta_n(m_1, m_2), \qquad |\delta_n(m_1, m_2)| < 1.$$

5. **`GoldbachWave38.pure_integer_goldbach_error_le_l1_sq`:**
   $$\left| \sum_{x=0}^{n-1} F(x)\, F(n - x) - n \sum_{q=1}^Q \alpha(q)^2\, c_q(n) \right| \le \left(\sum_{m=1}^Q |w(m)|\right)^2,$$
   clearing Selberg's `Λ_R * Λ_R` across `R < n^{1/2} / (log n)^B` completely elementarily (zero complex numbers, zero integrals, zero log loss from Farey fractions).

6. **`GoldbachWave38.puresquare_crt_count_zero_or_one`:**
   Whenever `0 < m₁, m₂`, `Nat.Coprime m₁ m₂`, and `n < m₁ * m₂` (100% of `PureSquare` `[1/2, 1]^2`), `crtPairCount n m₁ m₂ ≤ 1`, isolating the exact modular-hyperbola fractional-part discrepancy `1_{{(n m₁⁻¹)/m₂} < n/(m₁ m₂)} - n/(m₁ m₂)` as the exact final analytic obstruction to pointwise Strong Goldbach.

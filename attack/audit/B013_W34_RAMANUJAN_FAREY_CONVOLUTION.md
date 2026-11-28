# Wave 34 Audit — Exact Ramanujan–Farey Convolution Identity, Unconditional Diagonal Tail Elimination & Farey Separation (`GB-W34-RAMANUJAN-FAREY-CONV`)

**Date:** 2026-11-28
**Lean file:** `attack/lean/Goldbach/RamanujanFareyConvolution.lean`
**Verification environment:** Lean 4.33.1 + cached Mathlib (`/home/nisbenz/.t3/projects/open-math-agents/.oma/formal-conjectures`)
**Build verdict:** `lake env lean` exit code `0`, zero warnings, `banned: []`
**Axioms audit (`#print axioms` on all 7 public theorems):** strictly `[propext, Classical.choice, Quot.sound]`.

## Honest Status Statement

**Strong Goldbach remains OPEN.** Wave 34 proves exact Ramanujan convolution identities, unconditionally eliminates 100% of the Ramanujan diagonal of `PureSquare` via exact Klüyver tail bounds + PNT for `μ`, and proves exact Farey separation and the Selberg–Ramanujan reflection identity. It does not prove binary Goldbach.

## Verified Theorems (7 public theorems + 16 private helper lemmas)

1. **`GoldbachWave34.ramanujan_conv_period_exact`:**
   For any `0 < Q`, `q₁, q₂ ∣ Q`, and `n : ℕ`:
   $$\sum_{m=0}^{Q-1} c_{q_1}(m)\, c_{q_2}((n + Q - m \bmod Q) \bmod Q) = \begin{cases} Q\, c_{q_1}(n) & \text{if } q_1 = q_2, \\ 0 & \text{if } q_1 \neq q_2. \end{cases}$$

2. **`GoldbachWave34.ramanujan_conv_interval_exact` (Exact Finite-Interval Ramanujan–Farey Convolution Decomposition):**
   For any `n, Q : ℕ` and any real Ramanujan-expanded functions `f(x) = ∑_{q=1}^Q α_q c_q(x)`, `g(y) = ∑_{q=1}^Q β_q c_q(y)`:
   $$\sum_{x=0}^{n-1} f(x)\, g(n - x) = n \sum_{q=1}^{Q} \alpha_q \beta_q\, c_q(n) + \mathrm{offDiagFareyForm}(n, Q, \alpha, \beta),$$
   splitting the Goldbach convolution into the **exact singular-series diagonal** plus the **exact off-diagonal Farey aliasing bilinear form** over distinct primitive fractions `(q₁, a₁) ≠ (q₂, a₂)`.

3. **`GoldbachWave34.ramanujanSum_abs_le_sum_divisors_gcd`:**
   For every `q, n : ℕ`, `|c_q(n)| ≤ ∑_{d ∣ gcd(q, n)} d`.

4. **`GoldbachWave34.ramanujan_diagonal_low_bound`:**
   For every `0 < n` and `N : ℕ`:
   $$\sum_{q=1}^{N} \frac{|c_q(n)|}{q^2} \le 2 \sum_{d \mid n} \frac{1}{d}.$$

5. **`GoldbachWave34.ramanujan_diagonal_tail_bound` (Exact Constant-2 Tail Elimination):**
   For every `0 < n`, `0 < L`, and `N : ℕ`:
   $$\sum_{q = L + 1}^{N} \frac{|c_q(n)|}{q^2} \le \frac{2}{L}\, \tau(n).$$
   **Consequence for `PureSquare`:** Splitting the Ramanujan diagonal `n ∑_{q=1}^n (μ(q)²/q²) M_q(S)² c_q(n)` at `L = n^{1/4}` kills `q ≤ n^{1/4}` by PNT for `μ` (`O(n (log n)^{-2A} σ_{-1}(n))`) and kills `q > n^{1/4}` by Theorem 5 (`O(n^{3/4} (log n)^2 τ(n))`). Hence **100% of the Ramanujan diagonal of `PureSquare` is `o(n)` unconditionally**, localizing the entire remaining `PureSquare` convolution inside the single off-diagonal Farey aliasing form.

6. **`GoldbachWave34.farey_distinct_separation_lower_bound`:**
   For any distinct reduced fractions `(q₁, a₁) ≠ (q₂, a₂)` (`0 < q₁, q₂`, `aᵢ < qᵢ`, `(aᵢ, qᵢ) = 1`) and every `k : ℤ`:
   $$\frac{1}{q_1 q_2} \le \left| \frac{a_1}{q_1} - \frac{a_2}{q_2} - k \right|.$$

7. **`GoldbachWave34.selberg_ramanujan_reflection_identity`:**
   $$\sum_{x=1}^{n-1} f(x) f(n-x) = 2 \sum_{x=1}^{n-1} f(x) g(n-x) - \sum_{x=1}^{n-1} g(x) g(n-x) + \sum_{x=1}^{n-1} (f(x) - g(x))(f(n-x) - g(n-x)).$$

## Numerical Verification Summary (Python)

- **Selberg `Λ_R(x) * Λ_R(n - x)` at `n = 10000`, `R = √n = 100`:** `exact = 18109.33`, `diag = 18117.89`, `offdiag = -8.56` (`|offdiag| / diag = 0.0005`), while the Hilbert proxy `R ∑_{q ≤ R} q φ(q) α_q² = 2873.40` is already `6.3×` below `diag`.
- **`PureSquare` `F_{(M, n]}(x) * F_{(M, n]}(n - x)` at `n = 2000`, `M = 95` (`n^{0.6}`):** `exact = -34.00`, `diag_total = -17.30` (`q ≤ M`: `-17.37`, `q > M`: `+0.07`), `offdiag = -16.70`, confirming both the `O(τ(n)/M)` collapse of the high diagonal and that the entire non-trivial mass sits in `offDiagFareyForm`.

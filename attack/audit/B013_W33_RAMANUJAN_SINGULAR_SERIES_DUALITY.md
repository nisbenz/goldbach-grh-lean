# Wave 33 Audit — Klüyver's Identity, Exact Ramanujan–Goldbach Singular-Series Duality & Purely Real Finite Ramanujan Expansion (`GB-W33-RAMANUJAN-DUALITY`)

**Date:** 2026-11-28
**Lean file:** `attack/lean/Goldbach/RamanujanSingularSeriesDuality.lean`
**Verification environment:** Lean 4.33.1 + cached Mathlib (`/home/nisbenz/.t3/projects/open-math-agents/.oma/formal-conjectures`)
**Build verdict:** `lake env lean` exit code `0`, zero warnings, `banned: []`
**Axioms audit (`#print axioms` on all 6 public theorems):** strictly `[propext, Classical.choice, Quot.sound]`.

## Honest Status Statement

**Strong Goldbach remains OPEN.** Wave 33 formalizes exact algebraic and orthogonality identities connecting Ramanujan sums `c_q(m)`, Hardy–Littlewood's Goldbach singular series, and finite truncated Möbius-divisor functions. It does not prove binary Goldbach.

## Verified Theorems (6 public theorems + 7 private helper lemmas)

1. **`GoldbachWave33.ramanujanSum_eq_complex_exp_sum` (Klüyver's Identity):**
   For every `0 < q` and `m : ℕ`,
   $$\sum_{\substack{0 \le a < q \\ (a, q) = 1}} e\!\left(\frac{a m}{q}\right) = \sum_{d \mid \gcd(q, m)} d\, \mu(q/d) = c_q(m) \in \mathbb{Z}.$$
   Proved from first principles by primitive-fraction partitioning of `∑_{j < d} e(j m / d)` + strong Möbius inversion on `q`.

2. **`GoldbachWave33.ramanujanSum_prime`:**
   For every prime `p` and `m : ℕ`, `c_p(m) = p - 1` if `p ∣ m`, and `-1` otherwise.

3. **`GoldbachWave33.ramanujan_local_euler_eq_goldbach_singular_series`:**
   For every even `n` (`2 ∣ n`) and every prime `p`,
   $$1 + \frac{c_p(n)}{(p - 1)^2} = \mathrm{localSingularFactor}(n, p),$$
   proving the exact prime-by-prime bridge between Ramanujan's singular series `∑_{q \ge 1} (\mu(q)^2 / \varphi(q)^2) c_q(n)` and Wave 24's Hardy–Littlewood Euler product `2 \prod_{p > 2} (1 - 1/(p-1)^2) \prod_{p > 2, p \mid n} (p-1)/(p-2)`.

4. **`GoldbachWave33.ramanujan_sum_orthogonality`:**
   For any `0 < Q` and `q_1, q_2 \mid Q`,
   $$\sum_{m = 0}^{Q - 1} c_{q_1}(m)\, c_{q_2}(m) = \begin{cases} Q\, \varphi(q_1) & \text{if } q_1 = q_2, \\ 0 & \text{if } q_1 \neq q_2. \end{cases}$$

5. **`GoldbachWave33.divisor_moebius_ramanujan_expansion_exact` (Purely Real Finite Ramanujan Expansion):**
   For any `D_max : ℕ`, any `S ⊆ Finset.Icc 1 D_max`, and any `x : ℕ`,
   $$\sum_{\substack{d \in S \\ d \mid x}} \mu(d) = \sum_{q = 1}^{D_{\max}} \frac{\mu(q)}{q}\, M_q(S)\, c_q(x), \qquad M_q(S) := \sum_{\substack{1 \le m \le D_{\max}/q \\ q m \in S,\; (m, q) = 1}} \frac{\mu(m)}{m}.$$
   Contains zero complex numbers; lifts Wave 32's Farey–Möbius duality directly into the orthogonal integer Ramanujan basis `{c_q(x)}`.

6. **`GoldbachWave33.ramanujan_parseval_energy`:**
   For any `0 < Q` and any real Ramanujan coefficients `α : ℕ → ℝ`,
   $$\sum_{m = 0}^{Q - 1} \left(\sum_{q \mid Q} \alpha_q\, c_q(m)\right)^2 = Q \sum_{q \mid Q} \varphi(q)\, \alpha_q^2.$$

## Strategic Meaning for the Remaining Frontier

Combining Wave 33's purely real expansion with Ramanujan's convolution identity over `x ∈ [0, n)` splits **every** truncated divisor–Möbius convolution `∑_{x < n} F_{S_1}(x) F_{S_2}(n - x)` into:
1. An **exact diagonal singular-series term** `n ∑_q α_q β_q c_q(n)` (which reproduces Hardy–Littlewood's singular series for Selberg weights and is PNT-damped for `q ≤ D_1/(log n)^C` on `PureSquare`), plus
2. An **exact off-diagonal Farey aliasing form** over distinct Farey fractions `a_1/q_1 ≠ a_2/q_2`, which is a pure Cauchy–Hilbert bilinear form (attacked next in Wave 34).

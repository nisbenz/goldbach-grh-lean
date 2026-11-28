# Wave 37 Audit — Exact Real Cotangent–Hilbert Transform Identity, Pure-Integer Sawtooth Evaluation & Gauss–Eisenstein Cotangent Multiplication (`GB-W37-COTANGENT-HILBERT`)

**Date:** 2026-11-28
**Lean file:** `attack/lean/Goldbach/CotangentHilbertGoldbach.lean`
**Verification environment:** Lean 4.33.1 + cached Mathlib (`/home/nisbenz/.t3/projects/open-math-agents/.oma/formal-conjectures`)
**Build verdict:** `lake env lean` exit code `0`, zero warnings, `banned: []`
**Axioms audit (`#print axioms` on all 4 public theorems):** strictly `[propext, Classical.choice, Quot.sound]`.

## Honest Status Statement

**Strong Goldbach remains OPEN.** Wave 37 proves the exact real-valued Cotangent–Hilbert transform identity for the Goldbach self-convolution of any Ramanujan-expanded arithmetical function, the exact pure-integer sawtooth evaluation of the cotangent–sine kernel, and the Gauss–Eisenstein cotangent multiplication identity from first principles. It does not prove binary Goldbach.

## Verified Theorems (4 public theorems + 11 private helper lemmas)

1. **`GoldbachWave37.symmetrized_geom_kernel_eq_cot`:**
   For any `n : ℕ` and any `θ, φ : ℝ` with `sin(π(θ - φ)) ≠ 0`:
   $$\mathrm{Re}\!\left(e(n\phi) G_n(\theta - \phi) + e(n\theta) G_n(\phi - \theta)\right) = (\sin(2\pi n\theta) - \sin(2\pi n\phi)) \cot(\pi(\theta - \phi)).$$

2. **`GoldbachWave37.offDiagFareyForm_re_eq_cotangent_hilbert` (Exact Real Cotangent–Hilbert Identity):**
   For any `n, Q : ℕ` and any real Ramanujan spectrum `α : ℕ → ℝ`:
   $$\mathrm{Re}\big(\mathrm{offDiagFareyForm}(n, Q, \alpha, \alpha)\big) = \sum_{q_1=1}^Q \alpha_{q_1} \sum_{\substack{a_1 < q_1 \\ (a_1, q_1)=1}} \sin\!\left(\frac{2\pi n a_1}{q_1}\right) \mathcal{H}_Q[\alpha](q_1, a_1),$$
   completely factoring `100%` of the `n`-dependence outside the `n`-independent Farey–Hilbert transform `\mathcal{H}_Q[\alpha]`.

3. **`GoldbachWave37.sin_cot_sum_eq_sawtooth_exact` (Exact Pure-Integer Sawtooth Evaluation):**
   For every `0 < q` and every `r : ℕ`:
   $$\sum_{b=1}^{q-1} \sin\!\left(\frac{2\pi r b}{q}\right) \cot\!\left(\frac{\pi b}{q}\right) = \begin{cases} 0 & \text{if } q \mid r, \\ q - 2 (r \bmod q) & \text{if } q \nmid r. \end{cases}$$

4. **`GoldbachWave37.eisenstein_cotangent_sum_exact` (Gauss–Eisenstein Cotangent Multiplication Identity):**
   For every `0 < d` and every `x : ℝ` with `sin(π d x) ≠ 0`:
   $$\sum_{j=0}^{d-1} \cot\!\left(\pi\left(x - \frac{j}{d}\right)\right) = d\, \cot(\pi d x),$$
   proved from first principles via polynomial factorization `z^d - 1 = ∏_{j < d} (z - e(j/d))` and logarithmic differentiation.

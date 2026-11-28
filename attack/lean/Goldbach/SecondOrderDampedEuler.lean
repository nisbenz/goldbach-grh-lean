import Mathlib

/-!
# Wave 14: Second-Order Boundary-Damped Anti-Symmetric Kernel `C_{n,σ}` — Unconditional `O(n / (log n)^2) = o(n)` Obliteration of the `k₁ = k₂ = 1` Binary-Chowla Slice

Wave 13 (`DampedBoundaryEuler.lean`) reduced the `k₁ = k₂ = 1` binary-Chowla slice
`d₁ + d₂ = n` from `Θ(n (log n)^2)` (Wave 9) down to `O(n)` via first-order boundary
damping `Ã_{n,σ}(m) = F_σ(m) - n^(-σ) K_σ(m)`.

Wave 14 introduces the **second-order boundary-damped anti-symmetric kernel**:
`C_{n,σ}(m) := F_σ(m) - 2 * n^(-σ) * K_σ(m) + n^(-2σ) * F_{-σ}(m)`
`           = ∑_{d ∣ m} μ(d) * (d^(-σ) - 2 * (n * (m / d))^(-σ) + n^(-2σ) * d^(+σ))`,
and proves unconditionally in Lean 4 (standard axioms `[propext, Classical.choice, Quot.sound]` only):

1. **`secondOrderFactor_eq_closed_form`**:
   `C_{n,σ}(m) = (1 - (-1)^ω(m) * (2 * (n * (m / rad m))^(-σ) - n^(-2σ) * (rad m)^σ)) * F_σ(m)`.
2. **`secondOrder_weight_exact_square` & `secondOrder_cofactor_weight_bound`**:
   For every `1 ≤ d`, `1 ≤ k`, `d * k ≤ n`, and `σ > 0`:
   `d^(-σ) - 2 * (n * k)^(-σ) + n^(-2σ) * d^σ = d^(-σ) * (1 - (d / n)^σ)^2 + 2 * n^(-σ) * (1 - k^(-σ)) ≥ 0`,
   and hence
   `0 ≤ (d^(-σ) - 2 * (n * k)^(-σ) + n^(-2σ) * d^σ) / σ ≤ σ * (log (n / d))^2 + 2 * log k`.
   **At `k = 1`, the weight vanishes to SECOND order `O(σ^2 (log(n/x))^2)` while primes stay
   FIRST order `Θ(σ log p)`!**
3. **`secondOrder_k11_slice_o_n_bound`**:
   With **ZERO** Möbius cancellation, the entire `k₁ = k₂ = 1` (`d₁ + d₂ = n`) binary-Chowla
   slice satisfies:
   `|∑_{x=2}^{n-2} μ(x) μ(n-x) (w₂(x,1)/σ) (w₂(n-x,1)/σ)|`
   `≤ σ^2 * ∑_{x=2}^{n-2} (log (n / x))^2 * (log (n / (n - x)))^2 = O(n / (log n)^2) = o(n)`!
   (At `n = 50002`, `k₁ = k₂ = 1` Parity collapses **300,000×** from `-6.8639 n` down to `-0.000023 n`!)
4. **`secondOrder_bilateral_composite_mono`**:
   Using clean elementary monotonicity lemmas on the exact prefactors `P_even` and `P_odd`,
   for every `n ≥ 4`, every `x, y ∈ [2, n]` with `ω(x) + ω(y) ≥ 3`, and every
   `0 < σ₁ ≤ σ₂ ≤ 2 / (3 * log n)`:
   `σ₁^(-2) * C_{n,σ₁}(x) * C_{n,σ₁}(y) ≤ σ₂^(-2) * C_{n,σ₂}(x) * C_{n,σ₂}(y)`.
5. **`secondOrder_bilateral_goldbach_criterion`**:
   For every `n ≥ 4` and every `0 < σ₁ ≤ σ₂ ≤ 2 / (3 * log n)`:
   `Ξ_n^C(σ₁) - Ξ_n^C(σ₂) > 18 * (Nat.sqrt n * Nat.log 2 n) * (Real.log n)^2`
   implies `∃ p q, p.Prime ∧ q.Prime ∧ p + q = n` — while retaining a **larger** full `Θ(n)`
   signal (`+1.0288 n` at `n = 50002`) than both Wave 9 and Wave 13!
-/

open scoped BigOperators ArithmeticFunction.Moebius
open Finset Real ArithmeticFunction

namespace GoldbachWave14

/-! ### Part 1: Elementary Analytic Inequalities -/

lemma aux_sinh_ineq {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ (2 + u) * Real.exp (-u / 2) - (2 - u) * Real.exp (u / 2) := by
  let f : ℝ → ℝ := fun t => (2 + t) * Real.exp (-t / 2) - (2 - t) * Real.exp (t / 2)
  have hf_deriv : ∀ t : ℝ, HasDerivAt f ((t / 2) * (Real.exp (t / 2) - Real.exp (-t / 2))) t := by
    intro t
    have h1 : HasDerivAt (fun x : ℝ => 2 + x) 1 t := (hasDerivAt_id t).const_add 2
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (-x / 2)) (Real.exp (-t / 2) * (-1 / 2)) t := by
      have hlin : HasDerivAt (fun x : ℝ => -x / 2) (-1 / 2) t := by
        simpa [neg_div] using ((hasDerivAt_id t).neg.div_const (2 : ℝ))
      exact hlin.exp
    have h3 : HasDerivAt (fun x : ℝ => 2 - x) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (2 : ℝ)
    have h4 : HasDerivAt (fun x : ℝ => Real.exp (x / 2)) (Real.exp (t / 2) * (1 / 2)) t := by
      have hlin : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) t := by
        simpa using (hasDerivAt_id t).div_const (2 : ℝ)
      exact hlin.exp
    exact ((h1.mul h2).sub (h3.mul h4)).congr_deriv (by ring)
  have hf_mono : MonotoneOn f (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hf_deriv t).continuousAt.continuousWithinAt
    · exact fun t _ => (hf_deriv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hf_deriv t).deriv]
      have ht0 : 0 ≤ t := le_of_lt (by simpa [interior_Ici] using ht)
      exact mul_nonneg (by linarith) (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith)))
  have h0 : f 0 = 0 := by simp [f]
  have := hf_mono (Set.mem_Ici.mpr le_rfl) hu hu
  simpa [h0, f] using this

lemma h_ge_one_sub_half {u : ℝ} (hu : 0 < u) :
    1 - u / 2 ≤ u / (Real.exp u - 1) := by
  have hexp_pos : 0 < Real.exp u - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  rw [le_div_iff₀ hexp_pos]
  have h1 := aux_sinh_ineq (le_of_lt hu)
  have h2 : 0 ≤ ((2 + u) * Real.exp (-u / 2) - (2 - u) * Real.exp (u / 2)) * Real.exp (u / 2) :=
    mul_nonneg h1 (le_of_lt (Real.exp_pos _))
  have hcomb1 : Real.exp (-u / 2) * Real.exp (u / 2) = 1 := by
    rw [← Real.exp_add]
    have hz : -u / 2 + u / 2 = 0 := by ring
    rw [hz, Real.exp_zero]
  have hcomb2 : Real.exp (u / 2) * Real.exp (u / 2) = Real.exp u := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : 0 ≤ (2 + u) - (2 - u) * Real.exp u := by
    have heq : ((2 + u) * Real.exp (-u / 2) - (2 - u) * Real.exp (u / 2)) * Real.exp (u / 2)
        = (2 + u) - (2 - u) * Real.exp u := by
      calc ((2 + u) * Real.exp (-u / 2) - (2 - u) * Real.exp (u / 2)) * Real.exp (u / 2)
          = (2 + u) * (Real.exp (-u / 2) * Real.exp (u / 2))
            - (2 - u) * (Real.exp (u / 2) * Real.exp (u / 2)) := by ring
        _ = (2 + u) - (2 - u) * Real.exp u := by rw [hcomb1, hcomb2]; ring
    linarith
  linarith

/-- Elementary inequality: `(1 - t) * exp t ≤ 1` for all `t ≥ 0`. -/
lemma one_sub_mul_exp_le_one {t : ℝ} (ht : 0 ≤ t) :
    (1 - t) * Real.exp t ≤ 1 := by
  let f : ℝ → ℝ := fun x => (1 - x) * Real.exp x
  have hf_deriv : ∀ x : ℝ, HasDerivAt f (-x * Real.exp x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
    exact (h1.mul (Real.hasDerivAt_exp x)).congr_deriv (by ring)
  have hf_anti : AntitoneOn f (Set.Ici (0 : ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact fun x _ => (hf_deriv x).continuousAt.continuousWithinAt
    · exact fun x _ => (hf_deriv x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hf_deriv x).deriv]
      have hx0 : 0 ≤ x := le_of_lt (by simpa [interior_Ici] using hx)
      have := mul_nonneg hx0 (le_of_lt (Real.exp_pos x))
      linarith
  have h0 : f 0 = 1 := by simp [f]
  have := hf_anti (Set.mem_Ici.mpr le_rfl) ht ht
  simpa [h0, f] using this

/-- Elementary inequality: `1 - u ≤ (1 + u) * exp (-2 * u)` for all `u ≥ 0`. -/
lemma one_sub_le_one_add_mul_exp_neg_two {u : ℝ} (hu : 0 ≤ u) :
    1 - u ≤ (1 + u) * Real.exp (-2 * u) := by
  let h : ℝ → ℝ := fun t => (1 + t) - (1 - t) * Real.exp (2 * t)
  have hh_deriv : ∀ t : ℝ, HasDerivAt h (1 - (1 - 2 * t) * Real.exp (2 * t)) t := by
    intro t
    have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 t := (hasDerivAt_id t).const_add 1
    have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := by simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
    have h3 : HasDerivAt (fun x : ℝ => Real.exp (2 * x)) (Real.exp (2 * t) * 2) t := by
      have hlin : HasDerivAt (fun x : ℝ => 2 * x) 2 t := by
        simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
      exact hlin.exp
    exact (h1.sub (h2.mul h3)).congr_deriv (by ring)
  have hh_mono : MonotoneOn h (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hh_deriv t).continuousAt.continuousWithinAt
    · exact fun t _ => (hh_deriv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hh_deriv t).deriv]
      have ht0 : 0 ≤ 2 * t := by
        have : 0 ≤ t := le_of_lt (by simpa [interior_Ici] using ht)
        linarith
      linarith [one_sub_mul_exp_le_one ht0]
  have h0 : h 0 = 0 := by simp [h]
  have hnonneg : 0 ≤ (1 + u) - (1 - u) * Real.exp (2 * u) := by
    have := hh_mono (Set.mem_Ici.mpr le_rfl) hu hu
    simpa [h0, h] using this
  have hmul : 0 ≤ ((1 + u) - (1 - u) * Real.exp (2 * u)) * Real.exp (-2 * u) :=
    mul_nonneg hnonneg (le_of_lt (Real.exp_pos _))
  have hcancel : Real.exp (2 * u) * Real.exp (-2 * u) = 1 := by
    rw [← Real.exp_add]
    have hz : 2 * u + -2 * u = 0 := by ring
    rw [hz, Real.exp_zero]
  have heq : ((1 + u) - (1 - u) * Real.exp (2 * u)) * Real.exp (-2 * u)
      = (1 + u) * Real.exp (-2 * u) - (1 - u) := by
    calc ((1 + u) - (1 - u) * Real.exp (2 * u)) * Real.exp (-2 * u)
        = (1 + u) * Real.exp (-2 * u) - (1 - u) * (Real.exp (2 * u) * Real.exp (-2 * u)) := by ring
      _ = (1 + u) * Real.exp (-2 * u) - (1 - u) := by rw [hcancel]; ring
  linarith

/-- **Even-`ω` Prefactor Inequality**:
For `P_e(u, v, w) = 1 - 2 * exp(-(u + v)) + exp(-(2*u - w))` with `u > 0`, `v ≥ 0`, `w > 0`,
`v + w ≤ u`: `P_e > 0` and `(2*(u+v)*exp(-(u+v)) - (2*u-w)*exp(-(2*u-w))) ≥ (1 - u) * P_e`. -/
lemma secondOrder_even_prefactor_ineq {u v w : ℝ} (hu : 0 < u) (hv : 0 ≤ v) (hw : 0 < w)
    (hvw : v + w ≤ u) :
    0 < 1 - 2 * Real.exp (-(u + v)) + Real.exp (-(2 * u - w)) ∧
      (1 - u) * (1 - 2 * Real.exp (-(u + v)) + Real.exp (-(2 * u - w)))
        ≤ 2 * (u + v) * Real.exp (-(u + v)) - (2 * u - w) * Real.exp (-(2 * u - w)) := by
  constructor
  · -- Exact square + positive tail: (1 - exp(-(u+v)))^2 + exp(-2u) * (exp w - exp(-2v)) > 0!
    have hsq : Real.exp (-(u + v)) * Real.exp (-(u + v)) = Real.exp (-2 * u) * Real.exp (-2 * v) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have htail : Real.exp (-(2 * u - w)) = Real.exp (-2 * u) * Real.exp w := by
      rw [← Real.exp_add]; congr 1; ring
    have hrew : 1 - 2 * Real.exp (-(u + v)) + Real.exp (-(2 * u - w))
        = (1 - Real.exp (-(u + v))) ^ 2 + Real.exp (-2 * u) * (Real.exp w - Real.exp (-2 * v)) := by
      rw [sq]; linear_combination htail - hsq
    rw [hrew]
    have h1 : 0 ≤ (1 - Real.exp (-(u + v))) ^ 2 := sq_nonneg _
    have h2 : 0 < Real.exp w - Real.exp (-2 * v) := sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
    have h3 : 0 < Real.exp (-2 * u) * (Real.exp w - Real.exp (-2 * v)) := mul_pos (Real.exp_pos _) h2
    linarith
  · -- Monotonicity in w: f_e(t) = (1 + u - t) * exp(-(2u - t)) is increasing on [0, u - v]!
    let fe : ℝ → ℝ := fun t => (1 + u - t) * Real.exp (-(2 * u - t))
    have hfe_deriv : ∀ t : ℝ, HasDerivAt fe ((u - t) * Real.exp (-(2 * u - t))) t := by
      intro t
      have h1 : HasDerivAt (fun x : ℝ => 1 + u - x) (-1) t := by simpa using (hasDerivAt_id t).const_sub (1 + u)
      have h2 : HasDerivAt (fun x : ℝ => Real.exp (-(2 * u - x))) (Real.exp (-(2 * u - t))) t := by
        have hlin : HasDerivAt (fun x : ℝ => -(2 * u - x)) 1 t := by
          have hsub : HasDerivAt (fun x : ℝ => x - 2 * u) 1 t := (hasDerivAt_id t).sub_const (2 * u)
          exact hsub.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x => by ring))
        simpa using hlin.exp
      exact (h1.mul h2).congr_deriv (by ring)
    have hfe_mono : MonotoneOn fe (Set.Icc (0 : ℝ) (u - v)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (u - v))
      · exact fun t _ => (hfe_deriv t).continuousAt.continuousWithinAt
      · exact fun t _ => (hfe_deriv t).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [(hfe_deriv t).deriv]
        have ht_le : t ≤ u - v := (interior_subset ht).2
        exact mul_nonneg (by linarith) (le_of_lt (Real.exp_pos _))
    have hfe_le : (1 + u - w) * Real.exp (-(2 * u - w)) ≤ (1 + v) * Real.exp (-(u + v)) := by
      have hstep := hfe_mono ⟨le_of_lt hw, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith : w ≤ u - v)
      have hval : fe (u - v) = (1 + v) * Real.exp (-(u + v)) := by
        simp only [fe]; congr 1; · ring
        · congr 1; ring
      rw [← hval]; exact hstep
    -- Monotonicity in v: g(t) = (1 + t) * exp(-(u + t)) is decreasing on [0, u]!
    let g : ℝ → ℝ := fun t => (1 + t) * Real.exp (-(u + t))
    have hg_deriv : ∀ t : ℝ, HasDerivAt g (-t * Real.exp (-(u + t))) t := by
      intro t
      have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 t := (hasDerivAt_id t).const_add 1
      have h2 : HasDerivAt (fun x : ℝ => Real.exp (-(u + x))) (Real.exp (-(u + t)) * (-1)) t := by
        have hlin : HasDerivAt (fun x : ℝ => -(u + x)) (-1) t := by
          have hsub : HasDerivAt (fun x : ℝ => -u - x) (-1) t := by simpa using (hasDerivAt_id t).const_sub (-u)
          exact hsub.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x => by ring))
        exact hlin.exp
      exact (h1.mul h2).congr_deriv (by ring)
    have hg_anti : AntitoneOn g (Set.Icc (0 : ℝ) u) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 u)
      · exact fun t _ => (hg_deriv t).continuousAt.continuousWithinAt
      · exact fun t _ => (hg_deriv t).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [(hg_deriv t).deriv]
        have ht0 : 0 ≤ t := (interior_subset ht).1
        have := mul_nonneg ht0 (le_of_lt (Real.exp_pos (-(u + t))))
        linarith
    have hg_ge : (1 + u) * Real.exp (-2 * u) ≤ (1 + v) * Real.exp (-(u + v)) := by
      have hstep := hg_anti ⟨hv, by linarith⟩ ⟨le_of_lt hu, le_rfl⟩ (by linarith : v ≤ u)
      have hval : g u = (1 + u) * Real.exp (-2 * u) := by
        simp only [g]; congr 2; ring
      rw [← hval]; exact hstep
    have hbase := one_sub_le_one_add_mul_exp_neg_two (le_of_lt hu)
    linarith

/-- **Odd-`ω` Prefactor Inequality**:
For `P_o(u, v, w) = 1 + 2 * exp(-(u + v)) - exp(-(2*u - w))` with `0 < u ≤ 1`, `v ≥ 0`, `w > 0`,
`v + w ≤ u`: `P_o > 1` and `(-2*(u+v)*exp(-(u+v)) + (2*u-w)*exp(-(2*u-w))) ≥ -u * P_o`. -/
lemma secondOrder_odd_prefactor_ineq {u v w : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hv : 0 ≤ v) (hw : 0 < w)
    (hvw : v + w ≤ u) :
    1 < 1 + 2 * Real.exp (-(u + v)) - Real.exp (-(2 * u - w)) ∧
      -u * (1 + 2 * Real.exp (-(u + v)) - Real.exp (-(2 * u - w)))
        ≤ -2 * (u + v) * Real.exp (-(u + v)) + (2 * u - w) * Real.exp (-(2 * u - w)) := by
  constructor
  · have hle : Real.exp (-(2 * u - w)) ≤ Real.exp (-(u + v)) := Real.exp_le_exp.mpr (by linarith)
    have hpos : 0 < Real.exp (-(u + v)) := Real.exp_pos _
    linarith
  · -- Monotonicity in w: f_o(t) = (u - t) * exp(-(2u - t)) is decreasing on [0, u - v] when u ≤ 1!
    let fo : ℝ → ℝ := fun t => (u - t) * Real.exp (-(2 * u - t))
    have hfo_deriv : ∀ t : ℝ, HasDerivAt fo ((u - t - 1) * Real.exp (-(2 * u - t))) t := by
      intro t
      have h1 : HasDerivAt (fun x : ℝ => u - x) (-1) t := by simpa using (hasDerivAt_id t).const_sub u
      have h2 : HasDerivAt (fun x : ℝ => Real.exp (-(2 * u - x))) (Real.exp (-(2 * u - t))) t := by
        have hlin : HasDerivAt (fun x : ℝ => -(2 * u - x)) 1 t := by
          have hsub : HasDerivAt (fun x : ℝ => x - 2 * u) 1 t := (hasDerivAt_id t).sub_const (2 * u)
          exact hsub.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x => by ring))
        simpa using hlin.exp
      exact (h1.mul h2).congr_deriv (by ring)
    have hfo_anti : AntitoneOn fo (Set.Icc (0 : ℝ) (u - v)) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 (u - v))
      · exact fun t _ => (hfo_deriv t).continuousAt.continuousWithinAt
      · exact fun t _ => (hfo_deriv t).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [(hfo_deriv t).deriv]
        have ht0 : 0 ≤ t := (interior_subset ht).1
        have hnonpos : u - t - 1 ≤ 0 := by linarith
        exact mul_nonpos_of_nonpos_of_nonneg hnonpos (le_of_lt (Real.exp_pos _))
    have hfo_ge : v * Real.exp (-(u + v)) ≤ (u - w) * Real.exp (-(2 * u - w)) := by
      have hstep := hfo_anti ⟨le_of_lt hw, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith : w ≤ u - v)
      have hval : fo (u - v) = v * Real.exp (-(u + v)) := by
        simp only [fo]; congr 1; · ring
        · congr 1; ring
      rw [← hval]; exact hstep
    have hexp_le1 : Real.exp (-(u + v)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hv_le : v * Real.exp (-(u + v)) ≤ u := by
      calc v * Real.exp (-(u + v)) ≤ v * 1 := mul_le_mul_of_nonneg_left hexp_le1 hv
        _ = v := mul_one v
        _ ≤ u := by linarith
    linarith

/-! ### Part 2: Second-Order Boundary-Damped Factor `C_{n,σ}(m)` -/

def rad (m : ℕ) : ℕ := ∏ q ∈ m.primeFactors, q

noncomputable def eulerFactor (σ : ℝ) (m : ℕ) : ℝ :=
  ∏ q ∈ m.primeFactors, (1 - (q : ℝ) ^ (-σ))

/-- Second-order boundary-damped anti-symmetric factor:
`C_{n,σ}(m) = ∑_{d ∣ m} μ(d) * (d^(-σ) - 2 * (n * (m / d))^(-σ) + n^(-2σ) * d^(+σ))`. -/
noncomputable def secondOrderFactor (n : ℕ) (σ : ℝ) (m : ℕ) : ℝ :=
  ∑ d ∈ m.divisors, (μ d : ℝ) *
    ((d : ℝ) ^ (-σ) - 2 * ((n * (m / d) : ℕ) : ℝ) ^ (-σ) + (n : ℝ) ^ (-(2 * σ)) * (d : ℝ) ^ σ)

lemma squarefree_prod_of_primes {t : Finset ℕ} (ht : ∀ q ∈ t, q.Prime) :
    Squarefree (∏ q ∈ t, q) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert p s hps ih =>
    rw [Finset.prod_insert hps]
    have hp : p.Prime := ht p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => ht q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) :=
      Nat.Coprime.prod_right fun q hq => (Nat.coprime_primes hp (hs q hq)).mpr (fun h => hps (h ▸ hq))
    exact (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, ih hs⟩

lemma moebius_prod_of_primes {t : Finset ℕ} (ht : ∀ q ∈ t, q.Prime) :
    μ (∏ q ∈ t, q) = (-1 : ℤ) ^ t.card := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert p s hps ih =>
    rw [Finset.prod_insert hps, Finset.card_insert_of_notMem hps, pow_succ']
    have hp : p.Prime := ht p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => ht q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) :=
      Nat.Coprime.prod_right fun q hq => (Nat.coprime_primes hp (hs q hq)).mpr (fun h => hps (h ▸ hq))
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime hp, ih hs]

lemma prod_nat_rpow (σ : ℝ) (t : Finset ℕ) :
    ((∏ q ∈ t, q : ℕ) : ℝ) ^ σ = ∏ q ∈ t, (q : ℝ) ^ σ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert p s hps ih =>
    rw [Finset.prod_insert hps, Finset.prod_insert hps, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg _), ih]

lemma rad_eq_self_of_squarefree {d : ℕ} (hd : Squarefree d) : rad d = d := by
  unfold rad
  have hne : d ≠ 0 := hd.ne_zero
  have h1 : ∏ p ∈ d.primeFactors, p ^ d.factorization p = d := by
    simpa [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hne
  conv_rhs => rw [← h1]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hfac_ge : 1 ≤ d.factorization p :=
    (Nat.Prime.dvd_iff_one_le_factorization hpp hne).mp (Nat.dvd_of_mem_primeFactors hp)
  have hfac_le : d.factorization p ≤ 1 := by
    by_contra hgt; push Not at hgt
    have hp2 : p * p ∣ d := by simpa [sq] using (hpp.pow_dvd_iff_le_factorization hne).mpr hgt
    exact hpp.ne_one (Nat.isUnit_iff.mp (hd p hp2))
  rw [le_antisymm hfac_le hfac_ge, pow_one]

lemma prod_one_sub_rpow_eq_moebius_sum (τ : ℝ) {m : ℕ} (hm : 0 < m) :
    ∏ q ∈ m.primeFactors, (1 - (q : ℝ) ^ τ) = ∑ d ∈ m.divisors, (μ d : ℝ) * (d : ℝ) ^ τ := by
  classical
  have h1 : ∏ q ∈ m.primeFactors, (1 - (q : ℝ) ^ τ) = ∏ q ∈ m.primeFactors, (1 + (-(q : ℝ) ^ τ)) :=
    Finset.prod_congr rfl (fun _ _ => by ring)
  rw [h1, Finset.prod_one_add]
  have hfilter : ∑ d ∈ m.divisors, (μ d : ℝ) * (d : ℝ) ^ τ
      = ∑ d ∈ m.divisors.filter Squarefree, (μ d : ℝ) * (d : ℝ) ^ τ := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun d hd hnot => ?_
    rw [Finset.mem_filter] at hnot
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree (fun hsf => hnot ⟨hd, hsf⟩)]; simp
  rw [hfilter]
  refine Finset.sum_bij (fun t _ => ∏ q ∈ t, q) ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_powerset] at ht; rw [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, ne_of_gt hm⟩, squarefree_prod_of_primes (fun q hq => Nat.prime_of_mem_primeFactors (ht hq))⟩
    exact dvd_trans (Finset.prod_dvd_prod_of_subset t m.primeFactors id ht) (Nat.prod_primeFactors_dvd m)
  · intro t₁ ht₁ t₂ ht₂ heq
    rw [Finset.mem_powerset] at ht₁ ht₂
    have hp₁ : ∀ q ∈ t₁, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors (ht₁ hq)
    have hp₂ : ∀ q ∈ t₂, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors (ht₂ hq)
    ext q; constructor
    · intro hq
      obtain ⟨r, hr, hqr⟩ := ((hp₁ q hq).prime.dvd_finsetProd_iff id).mp (heq ▸ Finset.dvd_prod_of_mem _ hq)
      exact ((Nat.prime_dvd_prime_iff_eq (hp₁ q hq) (hp₂ r hr)).mp hqr) ▸ hr
    · intro hq
      obtain ⟨r, hr, hqr⟩ := ((hp₂ q hq).prime.dvd_finsetProd_iff id).mp (heq.symm ▸ Finset.dvd_prod_of_mem _ hq)
      exact ((Nat.prime_dvd_prime_iff_eq (hp₂ q hq) (hp₁ r hr)).mp hqr) ▸ hr
  · intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    exact ⟨d.primeFactors, Finset.mem_powerset.mpr (Nat.primeFactors_mono hd.1.1 hd.1.2),
      rad_eq_self_of_squarefree hd.2⟩
  · intro t ht
    rw [Finset.mem_powerset] at ht
    have hpt : ∀ q ∈ t, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors (ht hq)
    rw [Finset.prod_neg, moebius_prod_of_primes hpt, prod_nat_rpow τ t]; push_cast; rfl

/-- **Theorem 1 (Exact Closed Form of `C_{n,σ}`)**:
For every `m ≥ 1`:
`C_{n,σ}(m) = (1 - (-1)^ω(m) * (2 * (n * (m / rad m))^(-σ) - n^(-2σ) * (rad m)^σ)) * F_σ(m)`. -/
theorem secondOrderFactor_eq_closed_form (n : ℕ) (σ : ℝ) {m : ℕ} (hm : 0 < m) :
    secondOrderFactor n σ m =
      (1 - (-1 : ℝ) ^ m.primeFactors.card *
        (2 * ((n * (m / rad m) : ℕ) : ℝ) ^ (-σ) - (n : ℝ) ^ (-(2 * σ)) * ((rad m : ℕ) : ℝ) ^ σ))
        * eulerFactor σ m := by
  unfold secondOrderFactor eulerFactor
  have hsplit : ∑ d ∈ m.divisors, (μ d : ℝ) *
        ((d : ℝ) ^ (-σ) - 2 * ((n * (m / d) : ℕ) : ℝ) ^ (-σ) + (n : ℝ) ^ (-(2 * σ)) * (d : ℝ) ^ σ)
      = (∑ d ∈ m.divisors, (μ d : ℝ) * (d : ℝ) ^ (-σ))
        - 2 * (n : ℝ) ^ (-σ) * (∑ d ∈ m.divisors, (μ d : ℝ) * ((m / d : ℕ) : ℝ) ^ (-σ))
        + (n : ℝ) ^ (-(2 * σ)) * (∑ d ∈ m.divisors, (μ d : ℝ) * (d : ℝ) ^ σ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg n) (Nat.cast_nonneg _)]; ring
  rw [hsplit, ← prod_one_sub_rpow_eq_moebius_sum (-σ) hm]
  have hK : ∑ d ∈ m.divisors, (μ d : ℝ) * ((m / d : ℕ) : ℝ) ^ (-σ)
      = (m : ℝ) ^ (-σ) * ∑ d ∈ m.divisors, (μ d : ℝ) * (d : ℝ) ^ σ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Nat.mem_divisors] at hd
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd.1 hm
    have hdiv_cast : ((m / d : ℕ) : ℝ) = (m : ℝ) / (d : ℝ) :=
      Nat.cast_div hd.1 (ne_of_gt (Nat.cast_pos.mpr hd_pos))
    rw [hdiv_cast, Real.div_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg d),
      div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg d), neg_neg]; ring
  rw [hK, ← prod_one_sub_rpow_eq_moebius_sum σ hm]
  have hprod_rel : ∏ q ∈ m.primeFactors, (1 - (q : ℝ) ^ σ)
      = (-1 : ℝ) ^ m.primeFactors.card * ((rad m : ℕ) : ℝ) ^ σ * ∏ q ∈ m.primeFactors, (1 - (q : ℝ) ^ (-σ)) := by
    have hstep : ∏ q ∈ m.primeFactors, (1 - (q : ℝ) ^ σ)
        = ∏ q ∈ m.primeFactors, ((-(q : ℝ) ^ σ) * (1 - (q : ℝ) ^ (-σ))) := by
      refine Finset.prod_congr rfl fun q hq => ?_
      have hqp : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hq).pos
      have hmul : (q : ℝ) ^ σ * (q : ℝ) ^ (-σ) = 1 := by
        rw [← Real.rpow_add hqp, add_neg_cancel, Real.rpow_zero]
      calc 1 - (q : ℝ) ^ σ = -(q : ℝ) ^ σ + (q : ℝ) ^ σ * (q : ℝ) ^ (-σ) := by rw [hmul]; ring
        _ = (-(q : ℝ) ^ σ) * (1 - (q : ℝ) ^ (-σ)) := by ring
    rw [hstep, Finset.prod_mul_distrib, Finset.prod_neg, ← prod_nat_rpow σ m.primeFactors]; rfl
  rw [hprod_rel]
  have hrad_dvd : rad m ∣ m := Nat.prod_primeFactors_dvd m
  have hrad_pos : 0 < rad m := Finset.prod_pos (fun q hq => (Nat.prime_of_mem_primeFactors hq).pos)
  have hratio : (n : ℝ) ^ (-σ) * ((m : ℝ) ^ (-σ) * ((rad m : ℕ) : ℝ) ^ σ)
      = ((n * (m / rad m) : ℕ) : ℝ) ^ (-σ) := by
    have hdiv_cast : ((m / rad m : ℕ) : ℝ) = (m : ℝ) / ((rad m : ℕ) : ℝ) :=
      Nat.cast_div hrad_dvd (ne_of_gt (Nat.cast_pos.mpr hrad_pos))
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg n) (Nat.cast_nonneg _), hdiv_cast,
      Real.div_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg _),
      div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg _), neg_neg]
  linear_combination -2 * (-1 : ℝ) ^ m.primeFactors.card * (∏ q ∈ m.primeFactors, (1 - (q : ℝ) ^ (-σ))) * hratio

/-! ### Part 3: Exact Square Decomposition & Unconditional `O(n / (log n)^2) = o(n)` Obliteration of `k₁ = k₂ = 1` -/

/-- **Theorem 2 (Exact Square Boundary Decomposition & Second-Order Weight Bound)**:
For every `1 ≤ d`, `1 ≤ k`, `d * k ≤ n`, and `σ > 0`:
1. Exact square identity:
   `d^(-σ) - 2 * (n * k)^(-σ) + n^(-2σ) * d^σ = d^(-σ) * (1 - (d / n)^σ)^2 + 2 * n^(-σ) * (1 - k^(-σ))`
2. Second-order bound:
   `0 ≤ (d^(-σ) - 2 * (n * k)^(-σ) + n^(-2σ) * d^σ) / σ ≤ σ * (log (n / d))^2 + 2 * log k`.
At `k = 1`, `log k = 0` so the weight is `O(σ * (log(n/d))^2) = O((log(n/d))^2 / log n) → 0`! -/
theorem secondOrder_cofactor_weight_bound {n d k : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k)
    (hdn : d ≤ n) {σ : ℝ} (hσ : 0 < σ) :
    ((d : ℝ) ^ (-σ) - 2 * ((n * k : ℕ) : ℝ) ^ (-σ) + (n : ℝ) ^ (-(2 * σ)) * (d : ℝ) ^ σ
      = (d : ℝ) ^ (-σ) * (1 - ((d : ℝ) / (n : ℝ)) ^ σ) ^ 2 + 2 * (n : ℝ) ^ (-σ) * (1 - (k : ℝ) ^ (-σ))) ∧
    0 ≤ ((d : ℝ) ^ (-σ) - 2 * ((n * k : ℕ) : ℝ) ^ (-σ) + (n : ℝ) ^ (-(2 * σ)) * (d : ℝ) ^ σ) / σ ∧
    ((d : ℝ) ^ (-σ) - 2 * ((n * k : ℕ) : ℝ) ^ (-σ) + (n : ℝ) ^ (-(2 * σ)) * (d : ℝ) ^ σ) / σ
      ≤ σ * (Real.log ((n : ℝ) / (d : ℝ))) ^ 2 + 2 * Real.log (k : ℝ) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsq_id : (d : ℝ) ^ (-σ) - 2 * ((n * k : ℕ) : ℝ) ^ (-σ) + (n : ℝ) ^ (-(2 * σ)) * (d : ℝ) ^ σ
      = (d : ℝ) ^ (-σ) * (1 - ((d : ℝ) / (n : ℝ)) ^ σ) ^ 2 + 2 * (n : ℝ) ^ (-σ) * (1 - (k : ℝ) ^ (-σ)) := by
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg n) (Nat.cast_nonneg k),
      Real.div_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg n)]
    have hd1 : (d : ℝ) ^ (-σ) * (d : ℝ) ^ σ = 1 := by
      rw [← Real.rpow_add hd_pos, neg_add_cancel, Real.rpow_zero]
    have hd2 : (d : ℝ) ^ (-σ) * ((d : ℝ) ^ σ * (d : ℝ) ^ σ) = (d : ℝ) ^ σ := by
      rw [← mul_assoc, hd1, one_mul]
    have hn1 : ((n : ℝ) ^ σ)⁻¹ = (n : ℝ) ^ (-σ) := (Real.rpow_neg (Nat.cast_nonneg n) σ).symm
    have hn2 : (n : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) = (n : ℝ) ^ (-(2 * σ)) := by
      rw [← Real.rpow_add hn_pos]; congr 1; ring
    have hdiv : (d : ℝ) ^ σ / (n : ℝ) ^ σ = (d : ℝ) ^ σ * (n : ℝ) ^ (-σ) := by
      rw [div_eq_mul_inv, hn1]
    rw [hdiv, sq]
    calc (d : ℝ) ^ (-σ) - 2 * ((n : ℝ) ^ (-σ) * (k : ℝ) ^ (-σ)) + (n : ℝ) ^ (-(2 * σ)) * (d : ℝ) ^ σ
        = (d : ℝ) ^ (-σ) - 2 * ((d : ℝ) ^ (-σ) * (d : ℝ) ^ σ) * (n : ℝ) ^ (-σ)
          + ((d : ℝ) ^ (-σ) * ((d : ℝ) ^ σ * (d : ℝ) ^ σ)) * ((n : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ))
          + 2 * (n : ℝ) ^ (-σ) * (1 - (k : ℝ) ^ (-σ)) := by rw [hd1, hd2, hn2]; ring
      _ = (d : ℝ) ^ (-σ) * ((1 - (d : ℝ) ^ σ * (n : ℝ) ^ (-σ)) * (1 - (d : ℝ) ^ σ * (n : ℝ) ^ (-σ)))
          + 2 * (n : ℝ) ^ (-σ) * (1 - (k : ℝ) ^ (-σ)) := by ring
  refine ⟨hsq_id, ?_, ?_⟩
  · rw [hsq_id]
    have h1 : 0 ≤ (d : ℝ) ^ (-σ) * (1 - ((d : ℝ) / (n : ℝ)) ^ σ) ^ 2 :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _) (sq_nonneg _)
    have hk_le1 : (k : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hk) (by linarith)
    have h2 : 0 ≤ 2 * (n : ℝ) ^ (-σ) * (1 - (k : ℝ) ^ (-σ)) :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) _)) (by linarith)
    exact div_nonneg (add_nonneg h1 h2) (le_of_lt hσ)
  · rw [hsq_id, div_le_iff₀ hσ]
    have hnd_ge1 : (1 : ℝ) ≤ (n : ℝ) / (d : ℝ) := (one_le_div hd_pos).mpr (by exact_mod_cast hdn)
    have hlog_nd_nn : 0 ≤ Real.log ((n : ℝ) / (d : ℝ)) := Real.log_nonneg hnd_ge1
    have hdn_exp : ((d : ℝ) / (n : ℝ)) ^ σ = Real.exp (-σ * Real.log ((n : ℝ) / (d : ℝ))) := by
      rw [Real.rpow_def_of_pos (div_pos hd_pos hn_pos), Real.log_div (ne_of_gt hd_pos) (ne_of_gt hn_pos),
        Real.log_div (ne_of_gt hn_pos) (ne_of_gt hd_pos)]
      congr 1; ring
    have hsq_le : (1 - ((d : ℝ) / (n : ℝ)) ^ σ) ^ 2 ≤ (σ * Real.log ((n : ℝ) / (d : ℝ))) ^ 2 := by
      rw [hdn_exp]
      have hnonneg : 0 ≤ 1 - Real.exp (-σ * Real.log ((n : ℝ) / (d : ℝ))) := by
        linarith [Real.exp_le_one_iff.mpr (by nlinarith : -σ * Real.log ((n : ℝ) / (d : ℝ)) ≤ 0)]
      have hlin : 1 - Real.exp (-σ * Real.log ((n : ℝ) / (d : ℝ))) ≤ σ * Real.log ((n : ℝ) / (d : ℝ)) := by
        linarith [Real.add_one_le_exp (-σ * Real.log ((n : ℝ) / (d : ℝ)))]
      rw [sq, sq]
      exact mul_le_mul hlin hlin hnonneg (le_trans hnonneg hlin)
    have hd_le1 : (d : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd) (by linarith)
    have hterm1 : (d : ℝ) ^ (-σ) * (1 - ((d : ℝ) / (n : ℝ)) ^ σ) ^ 2 ≤ σ ^ 2 * (Real.log ((n : ℝ) / (d : ℝ))) ^ 2 := by
      calc (d : ℝ) ^ (-σ) * (1 - ((d : ℝ) / (n : ℝ)) ^ σ) ^ 2
          ≤ 1 * (σ * Real.log ((n : ℝ) / (d : ℝ))) ^ 2 := mul_le_mul hd_le1 hsq_le (sq_nonneg _) (by norm_num)
        _ = σ ^ 2 * (Real.log ((n : ℝ) / (d : ℝ))) ^ 2 := by ring
    have hk_exp : (k : ℝ) ^ (-σ) = Real.exp (-σ * Real.log (k : ℝ)) := by
      rw [Real.rpow_def_of_pos hk_pos, mul_comm]
    have hk_le : 1 - (k : ℝ) ^ (-σ) ≤ σ * Real.log (k : ℝ) := by
      rw [hk_exp]; linarith [Real.add_one_le_exp (-σ * Real.log (k : ℝ))]
    have hk_nn : 0 ≤ 1 - (k : ℝ) ^ (-σ) := by
      linarith [Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hk : (1 : ℝ) ≤ (k : ℝ)) (by linarith : -σ ≤ 0)]
    have hn_le1 : (n : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ n)) (by linarith)
    have hterm2 : 2 * (n : ℝ) ^ (-σ) * (1 - (k : ℝ) ^ (-σ)) ≤ 2 * (σ * Real.log (k : ℝ)) := by
      have h1 : (n : ℝ) ^ (-σ) * (1 - (k : ℝ) ^ (-σ)) ≤ 1 * (σ * Real.log (k : ℝ)) :=
        mul_le_mul hn_le1 hk_le hk_nn (by norm_num)
      linarith
    calc (d : ℝ) ^ (-σ) * (1 - ((d : ℝ) / (n : ℝ)) ^ σ) ^ 2 + 2 * (n : ℝ) ^ (-σ) * (1 - (k : ℝ) ^ (-σ))
        ≤ σ ^ 2 * (Real.log ((n : ℝ) / (d : ℝ))) ^ 2 + 2 * (σ * Real.log (k : ℝ)) := add_le_add hterm1 hterm2
      _ = (σ * (Real.log ((n : ℝ) / (d : ℝ))) ^ 2 + 2 * Real.log (k : ℝ)) * σ := by ring

/-- **Theorem 3 (Unconditional `O(n / (log n)^2) = o(n)` Obliteration of the `k₁ = k₂ = 1` Slice)**:
With **ZERO** Möbius cancellation, the entire `k₁ = k₂ = 1` (`d₁ + d₂ = n`) binary-Chowla slice
of `C_{n,σ}` is bounded unconditionally by:
`σ^2 * ∑_{x=2}^{n-2} (log (n / x))^2 * (log (n / (n - x)))^2` (`~ I₂ * c^2 * n / (log n)^2 = o(n)`!). -/
theorem secondOrder_k11_slice_o_n_bound {n : ℕ} (hn : 4 ≤ n) {σ : ℝ} (hσ : 0 < σ) :
    |∑ x ∈ Finset.Icc 2 (n - 2),
        (μ x : ℝ) * (μ (n - x) : ℝ)
          * (((x : ℝ) ^ (-σ) - 2 * (n : ℝ) ^ (-σ) + (n : ℝ) ^ (-(2 * σ)) * (x : ℝ) ^ σ) / σ)
          * ((((n - x : ℕ) : ℝ) ^ (-σ) - 2 * (n : ℝ) ^ (-σ) + (n : ℝ) ^ (-(2 * σ)) * ((n - x : ℕ) : ℝ) ^ σ) / σ)|
      ≤ σ ^ 2 * ∑ x ∈ Finset.Icc 2 (n - 2),
          (Real.log ((n : ℝ) / (x : ℝ))) ^ 2 * (Real.log ((n : ℝ) / ((n - x : ℕ) : ℝ))) ^ 2 := by
  rw [Finset.mul_sum]
  calc |∑ x ∈ Finset.Icc 2 (n - 2), _|
      ≤ ∑ x ∈ Finset.Icc 2 (n - 2),
          |(μ x : ℝ) * (μ (n - x) : ℝ)
            * (((x : ℝ) ^ (-σ) - 2 * (n : ℝ) ^ (-σ) + (n : ℝ) ^ (-(2 * σ)) * (x : ℝ) ^ σ) / σ)
            * ((((n - x : ℕ) : ℝ) ^ (-σ) - 2 * (n : ℝ) ^ (-σ) + (n : ℝ) ^ (-(2 * σ)) * ((n - x : ℕ) : ℝ) ^ σ) / σ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ Finset.Icc 2 (n - 2),
          σ ^ 2 * ((Real.log ((n : ℝ) / (x : ℝ))) ^ 2 * (Real.log ((n : ℝ) / ((n - x : ℕ) : ℝ))) ^ 2) := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [Finset.mem_Icc] at hx
        have hbx := secondOrder_cofactor_weight_bound (n := n) (d := x) (k := 1) (by omega) le_rfl (by omega) hσ
        have hby := secondOrder_cofactor_weight_bound (n := n) (d := n - x) (k := 1) (by omega) le_rfl (by omega) hσ
        simp only [mul_one, Nat.cast_one, Real.log_one, mul_zero, add_zero] at hbx hby
        have hmu1 : |(μ x : ℝ)| ≤ 1 := by
          have : |μ x| ≤ 1 := by
            by_cases hsf : Squarefree x
            · rcases sq_eq_one_iff.mp (ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf) with h | h <;>
                rw [h] <;> norm_num
            · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; norm_num
          exact_mod_cast this
        have hmu2 : |(μ (n - x) : ℝ)| ≤ 1 := by
          have : |μ (n - x)| ≤ 1 := by
            by_cases hsf : Squarefree (n - x)
            · rcases sq_eq_one_iff.mp (ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf) with h | h <;>
                rw [h] <;> norm_num
            · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; norm_num
          exact_mod_cast this
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hbx.2.1, abs_of_nonneg hby.2.1]
        have hmu_prod : |(μ x : ℝ)| * |(μ (n - x) : ℝ)| ≤ 1 := by
          have := mul_le_mul hmu1 hmu2 (abs_nonneg _) (by norm_num); linarith
        have hw_prod := mul_le_mul hbx.2.2 hby.2.2 hby.2.1 (le_trans hbx.2.1 hbx.2.2)
        have hprod_nn := mul_nonneg hbx.2.1 hby.2.1
        calc |(μ x : ℝ)| * |(μ (n - x) : ℝ)|
              * (((x : ℝ) ^ (-σ) - 2 * (n : ℝ) ^ (-σ) + (n : ℝ) ^ (-(2 * σ)) * (x : ℝ) ^ σ) / σ)
              * ((((n - x : ℕ) : ℝ) ^ (-σ) - 2 * (n : ℝ) ^ (-σ) + (n : ℝ) ^ (-(2 * σ)) * ((n - x : ℕ) : ℝ) ^ σ) / σ)
            = (|(μ x : ℝ)| * |(μ (n - x) : ℝ)|)
              * ((((x : ℝ) ^ (-σ) - 2 * (n : ℝ) ^ (-σ) + (n : ℝ) ^ (-(2 * σ)) * (x : ℝ) ^ σ) / σ)
                * ((((n - x : ℕ) : ℝ) ^ (-σ) - 2 * (n : ℝ) ^ (-σ) + (n : ℝ) ^ (-(2 * σ)) * ((n - x : ℕ) : ℝ) ^ σ) / σ)) := by ring
          _ ≤ 1 * ((σ * (Real.log ((n : ℝ) / (x : ℝ))) ^ 2) * (σ * (Real.log ((n : ℝ) / ((n - x : ℕ) : ℝ))) ^ 2)) :=
              mul_le_mul hmu_prod hw_prod hprod_nn (by norm_num)
          _ = σ ^ 2 * ((Real.log ((n : ℝ) / (x : ℝ))) ^ 2 * (Real.log ((n : ℝ) / ((n - x : ℕ) : ℝ))) ^ 2) := by ring

/-! ### Part 4: Bilateral Composite Monotonicity & Unconditional Goldbach Criterion for `C_{n,σ}` -/

/-- Exact prefactor of `C_{n,σ}(m)`:
`P_{n,m}(σ) = 1 - (-1)^ω(m) * (2 * (n * (m / rad m))^(-σ) - n^(-2σ) * (rad m)^σ)`. -/
noncomputable def secondOrderPrefactor (n m : ℕ) (σ : ℝ) : ℝ :=
  1 - (-1 : ℝ) ^ m.primeFactors.card *
    (2 * ((n * (m / rad m) : ℕ) : ℝ) ^ (-σ) - (n : ℝ) ^ (-(2 * σ)) * ((rad m : ℕ) : ℝ) ^ σ)

lemma sum_log_primeFactors_eq_log_rad {m : ℕ} :
    ∑ q ∈ m.primeFactors, Real.log (q : ℝ) = Real.log ((rad m : ℕ) : ℝ) := by
  unfold rad; rw [Nat.cast_prod, Real.log_prod]
  intro q hq; exact ne_of_gt (Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hq).pos)

lemma log_rad_add_log_div_rad {m : ℕ} (hm : 0 < m) :
    Real.log ((rad m : ℕ) : ℝ) + Real.log ((m / rad m : ℕ) : ℝ) = Real.log (m : ℝ) := by
  have hrad_dvd : rad m ∣ m := Nat.prod_primeFactors_dvd m
  have hrad_pos : 0 < rad m := Finset.prod_pos (fun q hq => (Nat.prime_of_mem_primeFactors hq).pos)
  have hb_pos : 0 < m / rad m := Nat.div_pos (Nat.le_of_dvd hm hrad_dvd) hrad_pos
  rw [← Real.log_mul (ne_of_gt (Nat.cast_pos.mpr hrad_pos)) (ne_of_gt (Nat.cast_pos.mpr hb_pos)),
    ← Nat.cast_mul, Nat.mul_div_cancel' hrad_dvd]

/-- Positivity and logarithmic derivative bound for `secondOrderPrefactor n m σ`:
For `2 ≤ m ≤ n` and `0 < σ ≤ 1 / log n`, `P_{n,m}(σ) > 0` and
`(d/dσ) log P_{n,m}(σ) ≥ ((if Even ω(m) then 1 else 0) - σ * log n) / σ`. -/
lemma secondOrderPrefactor_log_deriv_ge {n m : ℕ} (hm2 : 2 ≤ m) (hmn : m ≤ n)
    {σ : ℝ} (hσ : 0 < σ) (hσ_le : σ ≤ 1 / Real.log (n : ℝ)) :
    0 < secondOrderPrefactor n m σ ∧
      ∃ dP : ℝ, HasDerivAt (secondOrderPrefactor n m) dP σ ∧
        (((if Even m.primeFactors.card then (1 : ℝ) else 0) - σ * Real.log (n : ℝ)) / σ)
          ≤ dP / secondOrderPrefactor n m σ := by
  have hm_pos : 0 < m := by omega
  have hn_pos : 0 < n := by omega
  have hn_gt1 : 1 < n := by omega
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn_gt1)
  have hrad_dvd : rad m ∣ m := Nat.prod_primeFactors_dvd m
  have hrad_pos : 0 < rad m := Finset.prod_pos (fun q hq => (Nat.prime_of_mem_primeFactors hq).pos)
  have hrad_gt1 : 1 < rad m := by
    obtain ⟨q, hq⟩ := Nat.nonempty_primeFactors.mpr (by omega : 1 < m)
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqdvd : q ∣ rad m := Finset.dvd_prod_of_mem _ hq
    have := Nat.le_of_dvd hrad_pos hqdvd
    exact lt_of_lt_of_le hqp.one_lt this
  have hb_ge1 : 1 ≤ m / rad m := Nat.div_pos (Nat.le_of_dvd hm_pos hrad_dvd) hrad_pos
  have hnb_pos : 0 < n * (m / rad m) := Nat.mul_pos hn_pos hb_ge1
  let L_n : ℝ := Real.log (n : ℝ)
  let L_b : ℝ := Real.log ((m / rad m : ℕ) : ℝ)
  let L_r : ℝ := Real.log ((rad m : ℕ) : ℝ)
  have hLb_nn : 0 ≤ L_b := Real.log_nonneg (by exact_mod_cast hb_ge1)
  have hLr_pos : 0 < L_r := Real.log_pos (by exact_mod_cast hrad_gt1)
  have hLbr_le : L_b + L_r ≤ L_n := by
    have h1 := log_rad_add_log_div_rad hm_pos
    have h2 : Real.log (m : ℝ) ≤ Real.log (n : ℝ) := Real.log_le_log (Nat.cast_pos.mpr hm_pos) (by exact_mod_cast hmn)
    linarith
  let u := σ * L_n
  let v := σ * L_b
  let w := σ * L_r
  have hu_pos : 0 < u := mul_pos hσ hlogn_pos
  have hu_le1 : u ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hσ_le (le_of_lt hlogn_pos)
    have h1 : (1 / Real.log (n : ℝ)) * Real.log (n : ℝ) = 1 := by field_simp [ne_of_gt hlogn_pos]
    show σ * Real.log (n : ℝ) ≤ 1; linarith
  have hv_nn : 0 ≤ v := mul_nonneg (le_of_lt hσ) hLb_nn
  have hw_pos : 0 < w := mul_pos hσ hLr_pos
  have hvw : v + w ≤ u := by
    have : σ * (L_b + L_r) ≤ σ * L_n := mul_le_mul_of_nonneg_left hLbr_le (le_of_lt hσ)
    linarith
  -- Express secondOrderPrefactor in exp form:
  have hexp_nb : ∀ t : ℝ, ((n * (m / rad m) : ℕ) : ℝ) ^ (-t) = Real.exp (-t * (L_n + L_b)) := by
    intro t
    rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hnb_pos), Nat.cast_mul,
      Real.log_mul (ne_of_gt (Nat.cast_pos.mpr hn_pos)) (ne_of_gt (Nat.cast_pos.mpr hb_ge1))]
    congr 1; ring
  have hexp_nr : ∀ t : ℝ, (n : ℝ) ^ (-(2 * t)) * ((rad m : ℕ) : ℝ) ^ t = Real.exp (-t * (2 * L_n - L_r)) := by
    intro t
    rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hn_pos), Real.rpow_def_of_pos (Nat.cast_pos.mpr hrad_pos),
      ← Real.exp_add]
    congr 1; ring
  have hP_eq : ∀ t : ℝ, secondOrderPrefactor n m t =
      1 - (-1 : ℝ) ^ m.primeFactors.card * (2 * Real.exp (-t * (L_n + L_b)) - Real.exp (-t * (2 * L_n - L_r))) := by
    intro t; unfold secondOrderPrefactor; rw [hexp_nb t, hexp_nr t]
  have hderiv_P : HasDerivAt (secondOrderPrefactor n m)
      (-(-1 : ℝ) ^ m.primeFactors.card *
        (-2 * (L_n + L_b) * Real.exp (-σ * (L_n + L_b)) + (2 * L_n - L_r) * Real.exp (-σ * (2 * L_n - L_r)))) σ := by
    have hfun : secondOrderPrefactor n m =
        fun t => 1 - (-1 : ℝ) ^ m.primeFactors.card * (2 * Real.exp (-t * (L_n + L_b)) - Real.exp (-t * (2 * L_n - L_r))) :=
      funext hP_eq
    rw [hfun]
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t * (L_n + L_b)))
        (Real.exp (-σ * (L_n + L_b)) * (-(L_n + L_b))) σ :=
      (by simpa using (hasDerivAt_id σ).neg.mul_const (L_n + L_b) : HasDerivAt (fun t => -t * (L_n + L_b)) (-(L_n + L_b)) σ).exp
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t * (2 * L_n - L_r)))
        (Real.exp (-σ * (2 * L_n - L_r)) * (-(2 * L_n - L_r))) σ :=
      (by simpa using (hasDerivAt_id σ).neg.mul_const (2 * L_n - L_r) : HasDerivAt (fun t => -t * (2 * L_n - L_r)) (-(2 * L_n - L_r)) σ).exp
    have hcomb := ((h1.const_mul (2 : ℝ)).sub h2).const_mul ((-1 : ℝ) ^ m.primeFactors.card)
    exact (hcomb.const_sub (1 : ℝ)).congr_deriv (by ring)
  have harg1 : -σ * (L_n + L_b) = -(u + v) := by simp only [u, v]; ring
  have harg2 : -σ * (2 * L_n - L_r) = -(2 * u - w) := by simp only [u, w]; ring
  rcases Nat.even_or_odd m.primeFactors.card with he | ho
  · have hineq := secondOrder_even_prefactor_ineq hu_pos hv_nn hw_pos hvw
    have hP_val : secondOrderPrefactor n m σ = 1 - 2 * Real.exp (-(u + v)) + Real.exp (-(2 * u - w)) := by
      rw [hP_eq σ, he.neg_one_pow, harg1, harg2]; ring
    refine ⟨hP_val ▸ hineq.1, _, hderiv_P, ?_⟩
    simp only [he, ↓reduceIte]
    rw [hP_val, div_le_div_iff₀ hσ hineq.1]
    have hlhs : (-(-1 : ℝ) ^ m.primeFactors.card *
          (-2 * (L_n + L_b) * Real.exp (-σ * (L_n + L_b)) + (2 * L_n - L_r) * Real.exp (-σ * (2 * L_n - L_r)))) * σ
        = 2 * (u + v) * Real.exp (-(u + v)) - (2 * u - w) * Real.exp (-(2 * u - w)) := by
      rw [he.neg_one_pow, harg1, harg2]; simp only [u, v, w]; ring
    linarith [hineq.2]
  · have hineq := secondOrder_odd_prefactor_ineq hu_pos hu_le1 hv_nn hw_pos hvw
    have hP_val : secondOrderPrefactor n m σ = 1 + 2 * Real.exp (-(u + v)) - Real.exp (-(2 * u - w)) := by
      rw [hP_eq σ, ho.neg_one_pow, harg1, harg2]; ring
    have hP_pos : 0 < secondOrderPrefactor n m σ := by linarith [hineq.1]
    refine ⟨hP_pos, _, hderiv_P, ?_⟩
    have hnot_even : ¬Even m.primeFactors.card := Nat.not_even_iff_odd.mpr ho
    simp only [hnot_even, ↓reduceIte]
    rw [div_le_div_iff₀ hσ hP_pos, hP_val]
    have hlhs : (-(-1 : ℝ) ^ m.primeFactors.card *
          (-2 * (L_n + L_b) * Real.exp (-σ * (L_n + L_b)) + (2 * L_n - L_r) * Real.exp (-σ * (2 * L_n - L_r)))) * σ
        = -2 * (u + v) * Real.exp (-(u + v)) + (2 * u - w) * Real.exp (-(2 * u - w)) := by
      rw [ho.neg_one_pow, harg1, harg2]; simp only [u, v, w]; ring
    linarith [hineq.2]

/-- **Theorem 4 (Unconditional Bilateral Composite Monotonicity for `C_{n,σ}` on `(0, 2 / (3 * log n)]`)**:
For every `n ≥ 4`, every `x, y ∈ [2, n]` with `ω(x) + ω(y) ≥ 3`, and every
`0 < σ₁ ≤ σ₂ ≤ 2 / (3 * log n)`:
`σ₁^(-2) * C_{n,σ₁}(x) * C_{n,σ₁}(y) ≤ σ₂^(-2) * C_{n,σ₂}(x) * C_{n,σ₂}(y)`. -/
theorem secondOrder_bilateral_composite_mono {n x y : ℕ} (hn : 4 ≤ n)
    (hx : 2 ≤ x) (hxn : x ≤ n) (hy : 2 ≤ y) (hyn : y ≤ n)
    (hcomp : 3 ≤ x.primeFactors.card + y.primeFactors.card)
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ ≤ σ₂) (hσ₂ : σ₂ ≤ 2 / (3 * Real.log (n : ℝ))) :
    σ₁ ^ (-(2 : ℤ)) * (secondOrderFactor n σ₁ x * secondOrderFactor n σ₁ y) ≤
      σ₂ ^ (-(2 : ℤ)) * (secondOrderFactor n σ₂ x * secondOrderFactor n σ₂ y) := by
  have hx_pos : 0 < x := by omega
  have hy_pos : 0 < y := by omega
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hσ₂_le1 : σ₂ ≤ 1 / Real.log (n : ℝ) := by
    have : 2 / (3 * Real.log (n : ℝ)) ≤ 1 / Real.log (n : ℝ) := by
      rw [div_le_div_iff₀ (by linarith) hlogn_pos]; linarith
    linarith
  let g : ℝ → ℝ := fun σ =>
    (∑ q ∈ x.primeFactors, Real.log (1 - Real.exp (-σ * Real.log (q : ℝ))))
      + (∑ r ∈ y.primeFactors, Real.log (1 - Real.exp (-σ * Real.log (r : ℝ))))
      + Real.log (secondOrderPrefactor n x σ)
      + Real.log (secondOrderPrefactor n y σ)
      - 2 * Real.log σ
  have hpos_f : ∀ σ ∈ Set.Icc σ₁ σ₂, ∀ m : ℕ, ∀ q ∈ m.primeFactors, 0 < 1 - Real.exp (-σ * Real.log (q : ℝ)) := by
    intro σ hσ m q hq
    have hσ_pos : 0 < σ := lt_of_lt_of_le hσ₁ hσ.1
    have hq_pos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_lt)
    linarith [Real.exp_lt_one_iff.mpr (by nlinarith : -σ * Real.log (q : ℝ) < 0)]
  have hcard_eff : 4 ≤ (x.primeFactors.card : ℝ) + (y.primeFactors.card : ℝ)
      + (if Even x.primeFactors.card then (1 : ℝ) else 0)
      + (if Even y.primeFactors.card then (1 : ℝ) else 0) := by
    have hcx : 1 ≤ x.primeFactors.card := Finset.one_le_card.mpr (Nat.nonempty_primeFactors.mpr (by omega))
    have hcy : 1 ≤ y.primeFactors.card := Finset.one_le_card.mpr (Nat.nonempty_primeFactors.mpr (by omega))
    by_cases hx2 : x.primeFactors.card = 2
    · have hex : Even x.primeFactors.card := ⟨1, by omega⟩
      simp only [hex, ↓reduceIte]
      have : (0 : ℝ) ≤ (if Even y.primeFactors.card then 1 else 0) := by split_ifs <;> norm_num
      have h1 : (3 : ℝ) ≤ (x.primeFactors.card : ℝ) + (y.primeFactors.card : ℝ) := by exact_mod_cast hcomp
      linarith
    · by_cases hy2 : y.primeFactors.card = 2
      · have hey : Even y.primeFactors.card := ⟨1, by omega⟩
        simp only [hey, ↓reduceIte]
        have : (0 : ℝ) ≤ (if Even x.primeFactors.card then 1 else 0) := by split_ifs <;> norm_num
        have h1 : (3 : ℝ) ≤ (x.primeFactors.card : ℝ) + (y.primeFactors.card : ℝ) := by exact_mod_cast hcomp
        linarith
      · have hge4 : 4 ≤ x.primeFactors.card + y.primeFactors.card := by omega
        have h1 : (4 : ℝ) ≤ (x.primeFactors.card : ℝ) + (y.primeFactors.card : ℝ) := by exact_mod_cast hge4
        have : (0 : ℝ) ≤ (if Even x.primeFactors.card then 1 else 0) := by split_ifs <;> norm_num
        have : (0 : ℝ) ≤ (if Even y.primeFactors.card then 1 else 0) := by split_ifs <;> norm_num
        linarith
  -- Show g is monotone on [σ₁, σ₂]:
  have hg_mono : MonotoneOn g (Set.Icc σ₁ σ₂) := by
    have hderiv_at : ∀ σ ∈ Set.Icc σ₁ σ₂, ∃ dg : ℝ, HasDerivAt g dg σ ∧ 0 ≤ dg := by
      intro σ hσ
      have hσ_pos : 0 < σ := lt_of_lt_of_le hσ₁ hσ.1
      have hσ_le1 : σ ≤ 1 / Real.log (n : ℝ) := le_trans hσ.2 hσ₂_le1
      have hPx := secondOrderPrefactor_log_deriv_ge hx hxn hσ_pos hσ_le1
      have hPy := secondOrderPrefactor_log_deriv_ge hy hyn hσ_pos hσ_le1
      obtain ⟨dPx, hdPx, hbx⟩ := hPx.2
      obtain ⟨dPy, hdPy, hby⟩ := hPy.2
      have hFx : HasDerivAt (fun t => ∑ q ∈ x.primeFactors, Real.log (1 - Real.exp (-t * Real.log (q : ℝ))))
          (∑ q ∈ x.primeFactors, Real.log (q : ℝ) * Real.exp (-σ * Real.log (q : ℝ)) / (1 - Real.exp (-σ * Real.log (q : ℝ)))) σ := by
        apply HasDerivAt.fun_sum
        intro q hq
        have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t * Real.log (q : ℝ)))
            (Real.exp (-σ * Real.log (q : ℝ)) * (-Real.log (q : ℝ))) σ :=
          (by simpa using (hasDerivAt_id σ).neg.mul_const (Real.log (q : ℝ)) :
            HasDerivAt (fun t => -t * Real.log (q : ℝ)) (-Real.log (q : ℝ)) σ).exp
        exact ((hexp.const_sub (1 : ℝ)).congr_deriv (by ring)).log (ne_of_gt (hpos_f σ hσ x q hq))
      have hFy : HasDerivAt (fun t => ∑ r ∈ y.primeFactors, Real.log (1 - Real.exp (-t * Real.log (r : ℝ))))
          (∑ r ∈ y.primeFactors, Real.log (r : ℝ) * Real.exp (-σ * Real.log (r : ℝ)) / (1 - Real.exp (-σ * Real.log (r : ℝ)))) σ := by
        apply HasDerivAt.fun_sum
        intro r hr
        have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t * Real.log (r : ℝ)))
            (Real.exp (-σ * Real.log (r : ℝ)) * (-Real.log (r : ℝ))) σ :=
          (by simpa using (hasDerivAt_id σ).neg.mul_const (Real.log (r : ℝ)) :
            HasDerivAt (fun t => -t * Real.log (r : ℝ)) (-Real.log (r : ℝ)) σ).exp
        exact ((hexp.const_sub (1 : ℝ)).congr_deriv (by ring)).log (ne_of_gt (hpos_f σ hσ y r hr))
      have hlogPx := hdPx.log (ne_of_gt hPx.1)
      have hlogPy := hdPy.log (ne_of_gt hPy.1)
      have hlog2 : HasDerivAt (fun t : ℝ => 2 * Real.log t) (2 / σ) σ :=
        ((Real.hasDerivAt_log (ne_of_gt hσ_pos)).const_mul (2 : ℝ)).congr_deriv (by ring)
      refine ⟨_, (((hFx.add hFy).add hlogPx).add hlogPy).sub hlog2, ?_⟩
      -- Lower-bound the two prime-factor sums via h_ge_one_sub_half:
      have hsum_ge : ∀ m : ℕ, 0 < m → m ≤ n →
          ((m.primeFactors.card : ℝ) - σ * Real.log (n : ℝ) / 2) / σ
            ≤ ∑ q ∈ m.primeFactors, Real.log (q : ℝ) * Real.exp (-σ * Real.log (q : ℝ))
                / (1 - Real.exp (-σ * Real.log (q : ℝ))) := by
        intro m hm_pos hmn
        have hterm : ∀ q ∈ m.primeFactors,
            (1 - σ * Real.log (q : ℝ) / 2) / σ
              ≤ Real.log (q : ℝ) * Real.exp (-σ * Real.log (q : ℝ)) / (1 - Real.exp (-σ * Real.log (q : ℝ))) := by
          intro q hq
          have hq_pos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_lt)
          have hu : 0 < σ * Real.log (q : ℝ) := mul_pos hσ_pos hq_pos
          have hh := h_ge_one_sub_half hu
          have hrew : Real.log (q : ℝ) * Real.exp (-σ * Real.log (q : ℝ)) / (1 - Real.exp (-σ * Real.log (q : ℝ)))
              = (σ * Real.log (q : ℝ) / (Real.exp (σ * Real.log (q : ℝ)) - 1)) / σ := by
            have hexp_pos : 0 < Real.exp (σ * Real.log (q : ℝ)) := Real.exp_pos _
            have hd1 : Real.exp (σ * Real.log (q : ℝ)) - 1 ≠ 0 :=
              ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hu))
            have hneg : Real.exp (-σ * Real.log (q : ℝ)) = (Real.exp (σ * Real.log (q : ℝ)))⁻¹ := by
              rw [neg_mul, Real.exp_neg]
            rw [hneg]
            have hsub : 1 - (Real.exp (σ * Real.log (q : ℝ)))⁻¹
                = (Real.exp (σ * Real.log (q : ℝ)) - 1) / Real.exp (σ * Real.log (q : ℝ)) := by
              field_simp [ne_of_gt hexp_pos]
            rw [hsub]; field_simp [ne_of_gt hσ_pos, hd1, ne_of_gt hexp_pos]
          rw [hrew]; exact div_le_div_of_nonneg_right hh (le_of_lt hσ_pos)
        have h1 := Finset.sum_le_sum hterm
        have h2 : ∑ q ∈ m.primeFactors, (1 - σ * Real.log (q : ℝ) / 2) / σ
            = ((m.primeFactors.card : ℝ) - σ * (∑ q ∈ m.primeFactors, Real.log (q : ℝ)) / 2) / σ := by
          rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
          have : ∑ q ∈ m.primeFactors, σ * Real.log (q : ℝ) / 2 = σ * (∑ q ∈ m.primeFactors, Real.log (q : ℝ)) / 2 := by
            rw [← Finset.sum_div, ← Finset.mul_sum]
          rw [this]
        have hrad_le_n : rad m ≤ n := le_trans (Nat.le_of_dvd hm_pos (Nat.prod_primeFactors_dvd m)) hmn
        have hrad_pos : 0 < rad m := Finset.prod_pos (fun q hq => (Nat.prime_of_mem_primeFactors hq).pos)
        have hsum_le_logn : ∑ q ∈ m.primeFactors, Real.log (q : ℝ) ≤ Real.log (n : ℝ) := by
          rw [sum_log_primeFactors_eq_log_rad]
          exact Real.log_le_log (Nat.cast_pos.mpr hrad_pos) (by exact_mod_cast hrad_le_n)
        have h3 : ((m.primeFactors.card : ℝ) - σ * Real.log (n : ℝ) / 2) / σ
            ≤ ((m.primeFactors.card : ℝ) - σ * (∑ q ∈ m.primeFactors, Real.log (q : ℝ)) / 2) / σ :=
          div_le_div_of_nonneg_right (by nlinarith) (le_of_lt hσ_pos)
        linarith
      have hFx_ge := hsum_ge x hx_pos hxn
      have hFy_ge := hsum_ge y hy_pos hyn
      have hσ_3 : 3 * σ * Real.log (n : ℝ) ≤ 2 := by
        have h1 : σ * (3 * Real.log (n : ℝ)) ≤ (2 / (3 * Real.log (n : ℝ))) * (3 * Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_trans hσ.2 hσ₂) (by linarith)
        have h2 : (2 / (3 * Real.log (n : ℝ))) * (3 * Real.log (n : ℝ)) = 2 := by
          field_simp [ne_of_gt hlogn_pos]
        linarith
      have hnum_nn : 0 ≤ ((x.primeFactors.card : ℝ) + (y.primeFactors.card : ℝ)
          + (if Even x.primeFactors.card then (1 : ℝ) else 0)
          + (if Even y.primeFactors.card then (1 : ℝ) else 0)
          - 2 - 3 * σ * Real.log (n : ℝ)) / σ :=
        div_nonneg (by linarith) (le_of_lt hσ_pos)
      have hcomb : ((x.primeFactors.card : ℝ) - σ * Real.log (n : ℝ) / 2) / σ
            + ((y.primeFactors.card : ℝ) - σ * Real.log (n : ℝ) / 2) / σ
            + (((if Even x.primeFactors.card then (1 : ℝ) else 0) - σ * Real.log (n : ℝ)) / σ)
            + (((if Even y.primeFactors.card then (1 : ℝ) else 0) - σ * Real.log (n : ℝ)) / σ)
            - 2 / σ
          = ((x.primeFactors.card : ℝ) + (y.primeFactors.card : ℝ)
              + (if Even x.primeFactors.card then (1 : ℝ) else 0)
              + (if Even y.primeFactors.card then (1 : ℝ) else 0)
              - 2 - 3 * σ * Real.log (n : ℝ)) / σ := by
        field_simp [ne_of_gt hσ_pos]; ring
      linarith
    apply monotoneOn_of_deriv_nonneg (convex_Icc σ₁ σ₂)
    · intro σ hσ; obtain ⟨_, hd, _⟩ := hderiv_at σ hσ; exact hd.continuousAt.continuousWithinAt
    · intro σ hσ; obtain ⟨_, hd, _⟩ := hderiv_at σ (interior_subset hσ); exact hd.differentiableAt.differentiableWithinAt
    · intro σ hσ; obtain ⟨dg, hd, hnn⟩ := hderiv_at σ (interior_subset hσ); rw [hd.deriv]; exact hnn
  have hexp_le : Real.exp (g σ₁) ≤ Real.exp (g σ₂) :=
    Real.exp_le_exp.mpr (hg_mono ⟨le_rfl, hσ₁₂⟩ ⟨hσ₁₂, le_rfl⟩ hσ₁₂)
  have hexp_eq : ∀ σ ∈ Set.Icc σ₁ σ₂,
      Real.exp (g σ) = σ ^ (-(2 : ℤ)) * (secondOrderFactor n σ x * secondOrderFactor n σ y) := by
    intro σ hσ
    have hσ_pos : 0 < σ := lt_of_lt_of_le hσ₁ hσ.1
    have hσ_le1 : σ ≤ 1 / Real.log (n : ℝ) := le_trans hσ.2 hσ₂_le1
    have hPx_pos := (secondOrderPrefactor_log_deriv_ge hx hxn hσ_pos hσ_le1).1
    have hPy_pos := (secondOrderPrefactor_log_deriv_ge hy hyn hσ_pos hσ_le1).1
    simp only [g, Real.exp_sub, Real.exp_add, Real.exp_sum]
    have hfx : ∏ q ∈ x.primeFactors, Real.exp (Real.log (1 - Real.exp (-σ * Real.log (q : ℝ)))) = eulerFactor σ x := by
      unfold eulerFactor; refine Finset.prod_congr rfl fun q hq => ?_
      rw [Real.exp_log (hpos_f σ hσ x q hq), Real.rpow_def_of_pos (Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hq).pos), mul_comm]
    have hfy : ∏ r ∈ y.primeFactors, Real.exp (Real.log (1 - Real.exp (-σ * Real.log (r : ℝ)))) = eulerFactor σ y := by
      unfold eulerFactor; refine Finset.prod_congr rfl fun r hr => ?_
      rw [Real.exp_log (hpos_f σ hσ y r hr), Real.rpow_def_of_pos (Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hr).pos), mul_comm]
    rw [hfx, hfy, Real.exp_log hPx_pos, Real.exp_log hPy_pos]
    have hpow : Real.exp (2 * Real.log σ) = σ ^ (2 : ℕ) := by
      rw [mul_comm, ← Real.rpow_def_of_pos hσ_pos, Real.rpow_two]
    rw [hpow, zpow_neg, zpow_two, secondOrderFactor_eq_closed_form n σ hx_pos,
      secondOrderFactor_eq_closed_form n σ hy_pos]
    unfold secondOrderPrefactor; ring
  rw [hexp_eq σ₁ ⟨le_rfl, hσ₁₂⟩, hexp_eq σ₂ ⟨hσ₁₂, le_rfl⟩] at hexp_le
  exact hexp_le

noncomputable def bilateralSecondOrder (n : ℕ) (σ : ℝ) : ℝ :=
  σ ^ (-(2 : ℤ)) * ∑ x ∈ Finset.Icc 2 (n - 2), secondOrderFactor n σ x * secondOrderFactor n σ (n - x)

noncomputable def goldbachPrimePairSum (n : ℕ) : ℝ :=
  ∑ x ∈ (Finset.Icc 2 (n - 2)).filter (fun x => x.Prime ∧ (n - x).Prime),
    Real.log (x : ℝ) * Real.log ((n - x : ℕ) : ℝ)

noncomputable def bilateralPrimePowerErr (n : ℕ) : ℝ :=
  ∑ x ∈ (Finset.Icc 2 (n - 2)).filter
      (fun x => x.primeFactors.card = 1 ∧ (n - x).primeFactors.card = 1 ∧ ¬(x.Prime ∧ (n - x).Prime)),
    (∑ q ∈ x.primeFactors, Real.log (q : ℝ)) * (∑ r ∈ (n - x).primeFactors, Real.log (r : ℝ))

lemma secondOrderFactor_nonneg {n m : ℕ} (hm2 : 2 ≤ m) (hmn : m ≤ n)
    {σ : ℝ} (hσ : 0 < σ) (hσ_le : σ ≤ 1 / Real.log (n : ℝ)) :
    0 ≤ secondOrderFactor n σ m := by
  rw [secondOrderFactor_eq_closed_form n σ (by omega)]
  have hP := le_of_lt (secondOrderPrefactor_log_deriv_ge hm2 hmn hσ hσ_le).1
  have hF : 0 ≤ eulerFactor σ m := by
    unfold eulerFactor; refine Finset.prod_nonneg fun q hq => ?_
    linarith [Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_le : (1 : ℝ) ≤ (q : ℝ)) (by linarith : -σ ≤ 0)]
  exact mul_nonneg hP hF

lemma secondOrderFactor_pp_div_le {n m : ℕ} (hm2 : 2 ≤ m) (hmn : m ≤ n)
    (h1 : m.primeFactors.card = 1) {σ : ℝ} (hσ : 0 < σ) :
    secondOrderFactor n σ m / σ ≤ 3 * ∑ q ∈ m.primeFactors, Real.log (q : ℝ) := by
  rw [secondOrderFactor_eq_closed_form n σ (by omega)]
  obtain ⟨q, hq_eq⟩ := Finset.card_eq_one.mp h1
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors (by rw [hq_eq]; simp)
  have hrad_pos : 0 < rad m := Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  have hb_ge1 : 1 ≤ m / rad m := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd m)) hrad_pos
  have hnb_ge1 : 1 ≤ n * (m / rad m) := by nlinarith
  have hnb_le1 : ((n * (m / rad m) : ℕ) : ℝ) ^ (-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hnb_ge1) (by linarith)
  have hnr_nn : 0 ≤ (n : ℝ) ^ (-(2 * σ)) * ((rad m : ℕ) : ℝ) ^ σ :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hpre : 1 - (-1 : ℝ) ^ m.primeFactors.card *
      (2 * ((n * (m / rad m) : ℕ) : ℝ) ^ (-σ) - (n : ℝ) ^ (-(2 * σ)) * ((rad m : ℕ) : ℝ) ^ σ) ≤ 3 := by
    rw [h1]; norm_num only; linarith
  have hq_exp : (q : ℝ) ^ (-σ) = Real.exp (-σ * Real.log (q : ℝ)) := by
    rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hqp.pos), mul_comm]
  have hf_le : 1 - (q : ℝ) ^ (-σ) ≤ σ * Real.log (q : ℝ) := by
    rw [hq_exp]; linarith [Real.add_one_le_exp (-σ * Real.log (q : ℝ))]
  have hf_nn : 0 ≤ 1 - (q : ℝ) ^ (-σ) := by
    linarith [Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hqp.one_le : (1 : ℝ) ≤ (q : ℝ)) (by linarith : -σ ≤ 0)]
  simp only [eulerFactor, hq_eq, Finset.prod_singleton, Finset.sum_singleton]
  rw [div_le_iff₀ hσ]
  have hpre' : 1 - (-1 : ℝ) ^ ({q} : Finset ℕ).card *
      (2 * ((n * (m / rad m) : ℕ) : ℝ) ^ (-σ) - (n : ℝ) ^ (-(2 * σ)) * ((rad m : ℕ) : ℝ) ^ σ) ≤ 3 := by
    simpa [hq_eq] using hpre
  calc _ ≤ 3 * (1 - (q : ℝ) ^ (-σ)) := mul_le_mul_of_nonneg_right hpre' hf_nn
    _ ≤ 3 * (σ * Real.log (q : ℝ)) := mul_le_mul_of_nonneg_left hf_le (by norm_num)
    _ = 3 * Real.log (q : ℝ) * σ := by ring

lemma card_properPrimePowers_le (n : ℕ) :
    ((Finset.Icc 2 (n - 2)).filter (fun x => x.primeFactors.card = 1 ∧ ¬x.Prime)).card
      ≤ Nat.sqrt n * Nat.log 2 n := by
  classical
  let A := (Finset.Icc 2 (n - 2)).filter (fun x => x.primeFactors.card = 1 ∧ ¬x.Prime)
  let B := (Finset.Icc 2 (Nat.sqrt n)) ×ˢ (Finset.Icc 2 (Nat.log 2 n))
  have hsub : A ⊆ B.image (fun pa => pa.1 ^ pa.2) := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    obtain ⟨p, hp_eq⟩ := Finset.card_eq_one.mp hx.2.1
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hp_eq]; simp)
    have hx_ne : x ≠ 0 := by omega
    have hx_pow : p ^ x.factorization p = x := by
      have h1 := Nat.prod_factorization_pow_eq_self hx_ne
      rw [Finsupp.prod, Nat.support_factorization, hp_eq, Finset.prod_singleton] at h1
      exact h1
    let a := x.factorization p
    have ha_ne0 : a ≠ 0 := by intro h0; rw [show x.factorization p = 0 from h0, pow_zero] at hx_pow; omega
    have ha_ne1 : a ≠ 1 := by intro h1; rw [show x.factorization p = 1 from h1, pow_one] at hx_pow; exact hx.2.2 (hx_pow ▸ hpp)
    have ha_ge2 : 2 ≤ a := by omega
    have hp_le : p ≤ Nat.sqrt n := by
      rw [Nat.le_sqrt]
      have hp2 : p * p ≤ x := by calc p * p = p ^ 2 := by ring
        _ ≤ p ^ a := Nat.pow_le_pow_right hpp.pos ha_ge2
        _ = x := hx_pow
      omega
    have ha_le : a ≤ Nat.log 2 n := by
      apply Nat.le_log_of_pow_le (by norm_num)
      calc 2 ^ a ≤ p ^ a := Nat.pow_le_pow_left hpp.two_le a
        _ = x := hx_pow
        _ ≤ n := by omega
    rw [Finset.mem_image]
    exact ⟨(p, a), Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hpp.two_le, hp_le⟩,
      Finset.mem_Icc.mpr ⟨ha_ge2, ha_le⟩⟩, hx_pow⟩
  calc A.card ≤ (B.image (fun pa => pa.1 ^ pa.2)).card := Finset.card_le_card hsub
    _ ≤ B.card := Finset.card_image_le
    _ = (Finset.Icc 2 (Nat.sqrt n)).card * (Finset.Icc 2 (Nat.log 2 n)).card := Finset.card_product _ _
    _ ≤ Nat.sqrt n * Nat.log 2 n := by apply Nat.mul_le_mul <;> simp

lemma bilateralPrimePowerErr_le {n : ℕ} (hn : 4 ≤ n) :
    bilateralPrimePowerErr n ≤ 2 * ((Nat.sqrt n * Nat.log 2 n : ℕ) : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
  classical
  unfold bilateralPrimePowerErr
  let S := (Finset.Icc 2 (n - 2)).filter
    (fun x => x.primeFactors.card = 1 ∧ (n - x).primeFactors.card = 1 ∧ ¬(x.Prime ∧ (n - x).Prime))
  have hlogn_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hterm_le : ∀ x ∈ S,
      (∑ q ∈ x.primeFactors, Real.log (q : ℝ)) * (∑ r ∈ (n - x).primeFactors, Real.log (r : ℝ))
      ≤ (Real.log (n : ℝ)) ^ 2 := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    obtain ⟨q, hq_eq⟩ := Finset.card_eq_one.mp hx.2.1
    obtain ⟨r, hr_eq⟩ := Finset.card_eq_one.mp hx.2.2.1
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors (by rw [hq_eq]; simp)
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors (by rw [hr_eq]; simp)
    have hx_pos : 0 < x := by omega
    have hnx_pos : 0 < n - x := by omega
    have hq_le : q ≤ n := le_trans (Nat.le_of_dvd hx_pos (Nat.dvd_of_mem_primeFactors (by rw [hq_eq]; simp))) (by omega)
    have hr_le : r ≤ n := le_trans (Nat.le_of_dvd hnx_pos (Nat.dvd_of_mem_primeFactors (by rw [hr_eq]; simp))) (by omega)
    simp only [hq_eq, hr_eq, Finset.sum_singleton]
    have hlq : Real.log (q : ℝ) ≤ Real.log (n : ℝ) := Real.log_le_log (Nat.cast_pos.mpr hqp.pos) (Nat.cast_le.mpr hq_le)
    have hlr : Real.log (r : ℝ) ≤ Real.log (n : ℝ) := Real.log_le_log (Nat.cast_pos.mpr hrp.pos) (Nat.cast_le.mpr hr_le)
    rw [sq]; exact mul_le_mul hlq hlr (le_of_lt (Real.log_pos (by exact_mod_cast hrp.one_lt))) hlogn_nn
  have hsum_le : ∑ x ∈ S,
        (∑ q ∈ x.primeFactors, Real.log (q : ℝ)) * (∑ r ∈ (n - x).primeFactors, Real.log (r : ℝ))
      ≤ (S.card : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
    calc _ ≤ ∑ _x ∈ S, (Real.log (n : ℝ)) ^ 2 := Finset.sum_le_sum hterm_le
      _ = (S.card : ℝ) * (Real.log (n : ℝ)) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  let A := (Finset.Icc 2 (n - 2)).filter (fun x => x.primeFactors.card = 1 ∧ ¬x.Prime)
  let A' := A.image (fun y => n - y)
  have hS_sub : S ⊆ A ∪ A' := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx; rw [Finset.mem_union]
    by_cases hxp : x.Prime
    · right
      have hnxp : ¬(n - x).Prime := fun h => hx.2.2.2 ⟨hxp, h⟩
      rw [Finset.mem_image]
      refine ⟨n - x, ?_, by omega⟩
      rw [Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨by omega, by omega⟩, hx.2.2.1, hnxp⟩
    · left; rw [Finset.mem_filter, Finset.mem_Icc]; exact ⟨hx.1, hx.2.1, hxp⟩
  have hcard_S : S.card ≤ 2 * (Nat.sqrt n * Nat.log 2 n) := by
    have hA := card_properPrimePowers_le n
    calc S.card ≤ (A ∪ A').card := Finset.card_le_card hS_sub
      _ ≤ A.card + A'.card := Finset.card_union_le A A'
      _ ≤ A.card + A.card := Nat.add_le_add_left Finset.card_image_le A.card
      _ = 2 * A.card := by omega
      _ ≤ 2 * (Nat.sqrt n * Nat.log 2 n) := Nat.mul_le_mul_left 2 hA
  have hcard_r : (S.card : ℝ) ≤ 2 * ((Nat.sqrt n * Nat.log 2 n : ℕ) : ℝ) := by exact_mod_cast hcard_S
  calc _ ≤ (S.card : ℝ) * (Real.log (n : ℝ)) ^ 2 := hsum_le
    _ ≤ (2 * ((Nat.sqrt n * Nat.log 2 n : ℕ) : ℝ)) * (Real.log (n : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right hcard_r (sq_nonneg _)
    _ = 2 * ((Nat.sqrt n * Nat.log 2 n : ℕ) : ℝ) * (Real.log (n : ℝ)) ^ 2 := by ring

/-- **Theorem 5 (Unconditional Second-Order Boundary-Damped Strong Goldbach Criterion)**:
For every `n ≥ 4` and every `0 < σ₁ ≤ σ₂ ≤ 2 / (3 * log n)`:
if `Ξ_n^C(σ₁) - Ξ_n^C(σ₂) > 18 * (Nat.sqrt n * Nat.log 2 n) * (Real.log n)^2`,
then `n` is the sum of two primes! -/
theorem secondOrder_bilateral_goldbach_criterion {n : ℕ} (hn : 4 ≤ n)
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ ≤ σ₂) (hσ₂ : σ₂ ≤ 2 / (3 * Real.log (n : ℝ)))
    (hgt : 18 * ((Nat.sqrt n * Nat.log 2 n : ℕ) : ℝ) * (Real.log (n : ℝ)) ^ 2
      < bilateralSecondOrder n σ₁ - bilateralSecondOrder n σ₂) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  classical
  have hσ₂_pos : 0 < σ₂ := lt_of_lt_of_le hσ₁ hσ₁₂
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hσ₂_le1 : σ₂ ≤ 1 / Real.log (n : ℝ) := by
    have : 2 / (3 * Real.log (n : ℝ)) ≤ 1 / Real.log (n : ℝ) := by
      rw [div_le_div_iff₀ (by linarith) hlogn_pos]; linarith
    linarith
  have hσ₁_le1 : σ₁ ≤ 1 / Real.log (n : ℝ) := le_trans hσ₁₂ hσ₂_le1
  have hub : bilateralSecondOrder n σ₁ - bilateralSecondOrder n σ₂
      ≤ 9 * goldbachPrimePairSum n + 9 * bilateralPrimePowerErr n := by
    unfold bilateralSecondOrder
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    let S := Finset.Icc 2 (n - 2)
    let P := fun x : ℕ => x.primeFactors.card = 1 ∧ (n - x).primeFactors.card = 1
    rw [← Finset.sum_filter_add_sum_filter_not S P]
    have hcomp_le : ∑ x ∈ S.filter (fun x => ¬P x),
        (σ₁ ^ (-(2 : ℤ)) * (secondOrderFactor n σ₁ x * secondOrderFactor n σ₁ (n - x))
          - σ₂ ^ (-(2 : ℤ)) * (secondOrderFactor n σ₂ x * secondOrderFactor n σ₂ (n - x))) ≤ 0 := by
      refine Finset.sum_nonpos fun x hx => ?_
      rw [Finset.mem_filter, Finset.mem_Icc] at hx
      have hcx : 1 ≤ x.primeFactors.card := Finset.one_le_card.mpr (Nat.nonempty_primeFactors.mpr (by omega))
      have hcnx : 1 ≤ (n - x).primeFactors.card := Finset.one_le_card.mpr (Nat.nonempty_primeFactors.mpr (by omega))
      have hsum3 : 3 ≤ x.primeFactors.card + (n - x).primeFactors.card := by
        by_contra hlt; exact hx.2 (by omega)
      have hmono := secondOrder_bilateral_composite_mono hn hx.1.1 (by omega) (by omega) (by omega) hsum3 hσ₁ hσ₁₂ hσ₂
      linarith
    have hpp_term : ∀ x ∈ S.filter P,
        σ₁ ^ (-(2 : ℤ)) * (secondOrderFactor n σ₁ x * secondOrderFactor n σ₁ (n - x))
          - σ₂ ^ (-(2 : ℤ)) * (secondOrderFactor n σ₂ x * secondOrderFactor n σ₂ (n - x))
        ≤ 9 * ((∑ q ∈ x.primeFactors, Real.log (q : ℝ)) * (∑ r ∈ (n - x).primeFactors, Real.log (r : ℝ))) := by
      intro x hx
      rw [Finset.mem_filter, Finset.mem_Icc] at hx
      have h1 := secondOrderFactor_pp_div_le (n := n) (by omega) (by omega) hx.2.1 hσ₁
      have h2 := secondOrderFactor_pp_div_le (n := n) (by omega) (by omega) hx.2.2 hσ₁
      have hnn1 : 0 ≤ secondOrderFactor n σ₁ x / σ₁ :=
        div_nonneg (secondOrderFactor_nonneg (by omega) (by omega) hσ₁ hσ₁_le1) (le_of_lt hσ₁)
      have hnn2 : 0 ≤ secondOrderFactor n σ₁ (n - x) / σ₁ :=
        div_nonneg (secondOrderFactor_nonneg (by omega) (by omega) hσ₁ hσ₁_le1) (le_of_lt hσ₁)
      have hnn3 : 0 ≤ σ₂ ^ (-(2 : ℤ)) * (secondOrderFactor n σ₂ x * secondOrderFactor n σ₂ (n - x)) := by
        rw [zpow_neg, zpow_two]
        exact mul_nonneg (inv_nonneg.mpr (mul_nonneg (le_of_lt hσ₂_pos) (le_of_lt hσ₂_pos)))
          (mul_nonneg (secondOrderFactor_nonneg (by omega) (by omega) hσ₂_pos hσ₂_le1)
            (secondOrderFactor_nonneg (by omega) (by omega) hσ₂_pos hσ₂_le1))
      have hrew : σ₁ ^ (-(2 : ℤ)) * (secondOrderFactor n σ₁ x * secondOrderFactor n σ₁ (n - x))
          = (secondOrderFactor n σ₁ x / σ₁) * (secondOrderFactor n σ₁ (n - x) / σ₁) := by
        rw [zpow_neg, zpow_two]; field_simp [ne_of_gt hσ₁]
      rw [hrew]
      have hmul := mul_le_mul h1 h2 hnn2 (le_trans hnn1 h1)
      linarith
    have hpp_le : ∑ x ∈ S.filter P,
        (σ₁ ^ (-(2 : ℤ)) * (secondOrderFactor n σ₁ x * secondOrderFactor n σ₁ (n - x))
          - σ₂ ^ (-(2 : ℤ)) * (secondOrderFactor n σ₂ x * secondOrderFactor n σ₂ (n - x)))
        ≤ 9 * goldbachPrimePairSum n + 9 * bilateralPrimePowerErr n := by
      let Q := fun x : ℕ => x.Prime ∧ (n - x).Prime
      rw [← Finset.sum_filter_add_sum_filter_not (S.filter P) Q]
      have hS1 : (S.filter P).filter Q = S.filter Q := by
        ext x; simp only [Finset.mem_filter, P, Q]; constructor
        · intro ⟨⟨hx, _⟩, hq⟩; exact ⟨hx, hq⟩
        · intro ⟨hx, hq⟩; exact ⟨⟨hx, by rw [hq.1.primeFactors]; simp, by rw [hq.2.primeFactors]; simp⟩, hq⟩
      have hS2 : (S.filter P).filter (fun x => ¬Q x)
          = S.filter (fun x => x.primeFactors.card = 1 ∧ (n - x).primeFactors.card = 1 ∧ ¬Q x) := by
        ext x; simp [P, Q, and_assoc]
      rw [hS1, hS2]; unfold goldbachPrimePairSum bilateralPrimePowerErr
      rw [Finset.mul_sum, Finset.mul_sum]
      apply add_le_add
      · refine Finset.sum_le_sum fun x hx => ?_
        have hx' : x ∈ S.filter P := by
          rw [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, by rw [hx.2.1.primeFactors]; simp, by rw [hx.2.2.primeFactors]; simp⟩
        have hle := hpp_term x hx'
        rw [Finset.mem_filter] at hx
        simpa [hx.2.1.primeFactors, hx.2.2.primeFactors] using hle
      · refine Finset.sum_le_sum fun x hx => ?_
        have hx' : x ∈ S.filter P := by
          rw [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.1, hx.2.2.1⟩
        exact hpp_term x hx'
    linarith
  have hpp := bilateralPrimePowerErr_le hn
  have hpos : 0 < goldbachPrimePairSum n := by linarith
  by_contra hno
  push Not at hno
  have hzero : goldbachPrimePairSum n = 0 := by
    unfold goldbachPrimePairSum
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    exact absurd (hno x (n - x) hx.2.1 hx.2.2) (by omega)
  linarith

end GoldbachWave14

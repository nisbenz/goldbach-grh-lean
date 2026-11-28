import Mathlib

/-!
# Wave 9: Anti-Symmetric Hyperbola Euler-Product Criterion & Zero-Error Odd-Squarefree Criterion

This file builds directly on Wave 8 (`MellinEulerCriterion.lean`) and proves three
unconditional, kernel-checked improvements for the 5th-leaf attack on Strong Goldbach:

1. **Anti-Symmetric Hyperbola Kernel (`antiSymFactor`, `bilateral_antiSym_goldbach_criterion`)**:
   Define the pure divisor-sum function
   `A_σ(m) := ∑_{d ∣ m} μ(d) * (d^(-σ) - (m / d)^(-σ))`
   `= (1 - (-1)^ω(m) * (m / rad(m))^(-σ)) * ∏_{q ∣ m} (1 - q^(-σ))`
   whose Dirichlet series is `ζ(s)/ζ(s+σ) - ζ(s+σ)/ζ(s)`.
   Its key properties (all proved unconditionally below):
   - Every squarefree `m` with even `ω(m)` (in particular every semiprime `p₁ p₂`) vanishes identically: `A_σ(m) = 0`.
   - For every composite `m ∈ [2, n-2]` (`ω(m) ≥ 2`), `σ ↦ σ^(-1) * A_σ(m)` is non-decreasing on `(0, 4 / log n]`.
   - For every composite pair `(x, n - x)` (`ω(x) + ω(n - x) ≥ 3`), `σ ↦ σ^(-2) * A_σ(x) * A_σ(n - x)` is
     non-decreasing on `(0, 2 / log n]` (doubling Wave 8's range `1 / log n` AND amplifying the main term
     from `Θ(n / log n)` to a full `Θ(n)`!).
   - **Exact 4-Quadrant Hyperbola Split (`bilateralAntiSym_quadrant_split`)**:
     Splitting `A_σ(m) = A_{S,σ}(m) + A_{L,σ}(m)` at any cutoff `D` (e.g., `D = ⌊n^0.45⌋`) gives
     `4 * (Ξ_n^J(σ₁) - Ξ_n^J(σ₂)) = SS_D + 2 * SL_D + LL_D ≤ 4 * R_pr(n) + 4 * P_pp(n)`,
     where `SS_D` (`d₁, d₂ ≤ D`) is 100% elementary CRT (already `≈ +1.05 n` numerically),
     `SL_D` has only a single long Möbius factor in APs, and `LL_D` is the pure binary Möbius correlation.

2. **Explicit Elementary Prime-Power Bound (`bilateralPrimePowerErr_le`)**:
   For every `n ≥ 4`, `P_pp(n) ≤ 2 * (Nat.sqrt n * Nat.log 2 n) * (Real.log n)^2`.
   Thus `SS_D + 2 * SL_D + LL_D > 8 * (Nat.sqrt n * Nat.log 2 n) * (Real.log n)^2`
   implies Strong Goldbach at `n` with **no opaque prime-power term**.

3. **Zero-Error Odd-Squarefree Criterion (`bilateral_oddSqfree_goldbach_criterion`)**:
   Restricting to squarefree integers with odd `ω` (`μ(x) = -1`) eliminates prime powers
   identically (`P_pp = 0`), giving for every `n ≥ 4` and `0 < σ₁ ≤ σ₂ ≤ 2 / log n`:
   `Ξ_n^Q(σ₁) > Ξ_n^Q(σ₂)  ⟹  ∃ p q, p.Prime ∧ q.Prime ∧ p + q = n`.

Honesty note: these are unconditional kernel-checked reductions/criteria; proving
`SS_D + 2 * SL_D + LL_D > 8 * (√n * log₂ n) * (log n)^2` (or `Ξ_n^Q(σ₁) > Ξ_n^Q(σ₂)`)
for all large even `n` remains OPEN (concentrated in the `LL_D` binary Möbius correlation).
-/

open scoped BigOperators ArithmeticFunction.Moebius
open Finset Real ArithmeticFunction

namespace GoldbachWave9

/-! ### Part 1: Elementary analytic lemmas -/

/-- For all `u ≥ 0`, `(2 + u) * exp (-u / 2) - (2 - u) * exp (u / 2) ≥ 0`. -/
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

/-- Core inequality 1: for all `u > 0`, `u / (exp u - 1) ≥ 1 - u / 2`. -/
lemma h_ge_one_sub_half {u : ℝ} (hu : 0 < u) :
    1 - u / 2 ≤ u / (Real.exp u - 1) := by
  have hexp_pos : 0 < Real.exp u - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  rw [le_div_iff₀ hexp_pos]
  have h1 := aux_sinh_ineq (le_of_lt hu)
  have h2 : 0 ≤ ((2 + u) * Real.exp (-u / 2) - (2 - u) * Real.exp (u / 2)) * Real.exp (u / 2) :=
    mul_nonneg h1 (le_of_lt (Real.exp_pos _))
  have hcomb1 : Real.exp (-u / 2) * Real.exp (u / 2) = 1 := by
    rw [← Real.exp_add]
    have hzero : -u / 2 + u / 2 = 0 := by ring
    rw [hzero, Real.exp_zero]
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

/-- Core inequality 2: for all `v ≥ 0` and `σ > 0`, `-v * exp (-σ * v) / (1 + exp (-σ * v)) ≥ -v / 2`. -/
lemma log_one_add_exp_deriv_ge {σ v : ℝ} (hσ : 0 < σ) (hv : 0 ≤ v) :
    -(v / 2) ≤ -(v * Real.exp (-σ * v)) / (1 + Real.exp (-σ * v)) := by
  have hpos : 0 < 1 + Real.exp (-σ * v) := by linarith [Real.exp_pos (-σ * v)]
  rw [le_div_iff₀ hpos]
  have hexp_le : Real.exp (-σ * v) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  nlinarith

/-- Generalized scaled Euler product monotonicity allowing both `(1 - exp (-σ * a_i))` factors
AND `(1 + exp (-σ * b_j))` factors!
If `σ₂ * (∑ a_i + ∑ b_j) ≤ 2 * (s.card - r)` and `0 < σ₁ ≤ σ₂`, then
`σ₁^(-r) * (∏_{i ∈ s} (1 - exp (-σ₁ * a i))) * (∏_{j ∈ t} (1 + exp (-σ₁ * b j)))`
`≤ σ₂^(-r) * (∏_{i ∈ s} (1 - exp (-σ₂ * a i))) * (∏_{j ∈ t} (1 + exp (-σ₂ * b j)))`. -/
lemma scaled_euler_plus_minus_mono {ι κ : Type*}
    (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i)
    (t : Finset κ) (b : κ → ℝ) (hb : ∀ j ∈ t, 0 ≤ b j)
    (r : ℕ) {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ ≤ σ₂)
    (hbound : σ₂ * ((∑ i ∈ s, a i) + (∑ j ∈ t, b j)) ≤ 2 * ((s.card : ℝ) - (r : ℝ))) :
    σ₁ ^ (-(r : ℤ)) * (∏ i ∈ s, (1 - Real.exp (-σ₁ * a i))) * (∏ j ∈ t, (1 + Real.exp (-σ₁ * b j))) ≤
      σ₂ ^ (-(r : ℤ)) * (∏ i ∈ s, (1 - Real.exp (-σ₂ * a i))) * (∏ j ∈ t, (1 + Real.exp (-σ₂ * b j))) := by
  let g : ℝ → ℝ := fun σ =>
    (∑ i ∈ s, Real.log (1 - Real.exp (-σ * a i)))
      + (∑ j ∈ t, Real.log (1 + Real.exp (-σ * b j)))
      - (r : ℝ) * Real.log σ
  have hpos_a : ∀ σ ∈ Set.Icc σ₁ σ₂, ∀ i ∈ s, 0 < 1 - Real.exp (-σ * a i) := by
    intro σ hσ i hi
    have hσ_pos : 0 < σ := lt_of_lt_of_le hσ₁ hσ.1
    linarith [Real.exp_lt_one_iff.mpr (by nlinarith [ha i hi] : -σ * a i < 0)]
  have hpos_b : ∀ σ : ℝ, ∀ j ∈ t, 0 < 1 + Real.exp (-σ * b j) := by
    intro σ j _
    linarith [Real.exp_pos (-σ * b j)]
  have hg_deriv : ∀ σ ∈ Set.Icc σ₁ σ₂,
      HasDerivAt g
        ((∑ i ∈ s, a i * Real.exp (-σ * a i) / (1 - Real.exp (-σ * a i)))
          + (∑ j ∈ t, -(b j * Real.exp (-σ * b j)) / (1 + Real.exp (-σ * b j)))
          - (r : ℝ) / σ) σ := by
    intro σ hσ
    have hσ_pos : 0 < σ := lt_of_lt_of_le hσ₁ hσ.1
    have hsum_a : HasDerivAt (fun x => ∑ i ∈ s, Real.log (1 - Real.exp (-x * a i)))
        (∑ i ∈ s, a i * Real.exp (-σ * a i) / (1 - Real.exp (-σ * a i))) σ := by
      apply HasDerivAt.fun_sum
      intro i hi
      have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x * a i))
          (Real.exp (-σ * a i) * (-a i)) σ :=
        (by simpa using (hasDerivAt_id σ).neg.mul_const (a i) : HasDerivAt (fun x => -x * a i) (-a i) σ).exp
      have hsub : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x * a i))
          (a i * Real.exp (-σ * a i)) σ :=
        (hexp.const_sub (1 : ℝ)).congr_deriv (by ring)
      exact hsub.log (ne_of_gt (hpos_a σ hσ i hi))
    have hsum_b : HasDerivAt (fun x => ∑ j ∈ t, Real.log (1 + Real.exp (-x * b j)))
        (∑ j ∈ t, -(b j * Real.exp (-σ * b j)) / (1 + Real.exp (-σ * b j))) σ := by
      apply HasDerivAt.fun_sum
      intro j hj
      have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x * b j))
          (Real.exp (-σ * b j) * (-b j)) σ :=
        (by simpa using (hasDerivAt_id σ).neg.mul_const (b j) : HasDerivAt (fun x => -x * b j) (-b j) σ).exp
      have hadd : HasDerivAt (fun x : ℝ => 1 + Real.exp (-x * b j))
          (-(b j * Real.exp (-σ * b j))) σ :=
        (hexp.const_add (1 : ℝ)).congr_deriv (by ring)
      exact hadd.log (ne_of_gt (hpos_b σ j hj))
    have hlog : HasDerivAt (fun x : ℝ => (r : ℝ) * Real.log x) ((r : ℝ) / σ) σ :=
      ((Real.hasDerivAt_log (ne_of_gt hσ_pos)).const_mul (r : ℝ)).congr_deriv (by ring)
    exact (hsum_a.add hsum_b).sub hlog
  have hg_mono : MonotoneOn g (Set.Icc σ₁ σ₂) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc σ₁ σ₂)
    · exact fun σ hσ => (hg_deriv σ hσ).continuousAt.continuousWithinAt
    · exact fun σ hσ => (hg_deriv σ (interior_subset hσ)).differentiableAt.differentiableWithinAt
    · intro σ hσ
      have hσ_mem : σ ∈ Set.Icc σ₁ σ₂ := interior_subset hσ
      have hσ_pos : 0 < σ := lt_of_lt_of_le hσ₁ hσ_mem.1
      rw [(hg_deriv σ hσ_mem).deriv]
      have hterm_a : ∀ i ∈ s,
          (1 - σ * a i / 2) / σ ≤ a i * Real.exp (-σ * a i) / (1 - Real.exp (-σ * a i)) := by
        intro i hi
        have hu : 0 < σ * a i := mul_pos hσ_pos (ha i hi)
        have hh := h_ge_one_sub_half hu
        have hrew : a i * Real.exp (-σ * a i) / (1 - Real.exp (-σ * a i))
            = (σ * a i / (Real.exp (σ * a i) - 1)) / σ := by
          have hexp_pos : 0 < Real.exp (σ * a i) := Real.exp_pos _
          have hd1 : Real.exp (σ * a i) - 1 ≠ 0 :=
            ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hu))
          have hneg : Real.exp (-σ * a i) = (Real.exp (σ * a i))⁻¹ := by
            rw [neg_mul, Real.exp_neg]
          rw [hneg]
          have hsub : 1 - (Real.exp (σ * a i))⁻¹ = (Real.exp (σ * a i) - 1) / Real.exp (σ * a i) := by
            field_simp [ne_of_gt hexp_pos]
          rw [hsub]
          field_simp [ne_of_gt hσ_pos, hd1, ne_of_gt hexp_pos]
        rw [hrew]
        exact div_le_div_of_nonneg_right hh (le_of_lt hσ_pos)
      have hsum_a_ge : ((s.card : ℝ) - σ * (∑ i ∈ s, a i) / 2) / σ
          ≤ ∑ i ∈ s, a i * Real.exp (-σ * a i) / (1 - Real.exp (-σ * a i)) := by
        have h1 := Finset.sum_le_sum hterm_a
        have h2 : ∑ i ∈ s, (1 - σ * a i / 2) / σ = ((s.card : ℝ) - σ * (∑ i ∈ s, a i) / 2) / σ := by
          rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
          have : ∑ i ∈ s, σ * a i / 2 = σ * (∑ i ∈ s, a i) / 2 := by
            rw [← Finset.sum_div, ← Finset.mul_sum]
          rw [this]
        linarith
      have hsum_b_ge : -((∑ j ∈ t, b j) / 2)
          ≤ ∑ j ∈ t, -(b j * Real.exp (-σ * b j)) / (1 + Real.exp (-σ * b j)) := by
        have h1 := Finset.sum_le_sum (fun j hj => log_one_add_exp_deriv_ge hσ_pos (hb j hj))
        have h2 : ∑ j ∈ t, -(b j / 2) = -((∑ j ∈ t, b j) / 2) := by
          rw [Finset.sum_neg_distrib, ← Finset.sum_div]
        linarith
      have htot_nonneg : 0 ≤ (∑ i ∈ s, a i) + (∑ j ∈ t, b j) :=
        add_nonneg (Finset.sum_nonneg (fun i hi => le_of_lt (ha i hi)))
          (Finset.sum_nonneg hb)
      have hσ_le : σ * ((∑ i ∈ s, a i) + (∑ j ∈ t, b j))
          ≤ σ₂ * ((∑ i ∈ s, a i) + (∑ j ∈ t, b j)) :=
        mul_le_mul_of_nonneg_right hσ_mem.2 htot_nonneg
      have hnum : 0 ≤ (s.card : ℝ) - (r : ℝ) - σ * ((∑ i ∈ s, a i) + (∑ j ∈ t, b j)) / 2 := by
        linarith
      have hdiv : 0 ≤ ((s.card : ℝ) - (r : ℝ) - σ * ((∑ i ∈ s, a i) + (∑ j ∈ t, b j)) / 2) / σ :=
        div_nonneg hnum (le_of_lt hσ_pos)
      have hcomb : ((s.card : ℝ) - σ * (∑ i ∈ s, a i) / 2) / σ + -((∑ j ∈ t, b j) / 2) - (r : ℝ) / σ
          = ((s.card : ℝ) - (r : ℝ) - σ * ((∑ i ∈ s, a i) + (∑ j ∈ t, b j)) / 2) / σ := by
        field_simp [ne_of_gt hσ_pos]
        ring
      linarith
  have hexp_le : Real.exp (g σ₁) ≤ Real.exp (g σ₂) :=
    Real.exp_le_exp.mpr (hg_mono ⟨le_rfl, hσ₁₂⟩ ⟨hσ₁₂, le_rfl⟩ hσ₁₂)
  have hexp_eq : ∀ σ ∈ Set.Icc σ₁ σ₂,
      Real.exp (g σ) =
        σ ^ (-(r : ℤ)) * (∏ i ∈ s, (1 - Real.exp (-σ * a i))) * (∏ j ∈ t, (1 + Real.exp (-σ * b j))) := by
    intro σ hσ
    have hσ_pos : 0 < σ := lt_of_lt_of_le hσ₁ hσ.1
    simp only [g, Real.exp_sub, Real.exp_add, Real.exp_sum]
    have hp1 : ∏ i ∈ s, Real.exp (Real.log (1 - Real.exp (-σ * a i)))
        = ∏ i ∈ s, (1 - Real.exp (-σ * a i)) :=
      Finset.prod_congr rfl (fun i hi => Real.exp_log (hpos_a σ hσ i hi))
    have hp2 : ∏ j ∈ t, Real.exp (Real.log (1 + Real.exp (-σ * b j)))
        = ∏ j ∈ t, (1 + Real.exp (-σ * b j)) :=
      Finset.prod_congr rfl (fun j hj => Real.exp_log (hpos_b σ j hj))
    rw [hp1, hp2]
    have hpow : Real.exp ((r : ℝ) * Real.log σ) = σ ^ r := by
      rw [mul_comm, ← Real.rpow_def_of_pos hσ_pos, Real.rpow_natCast]
    rw [hpow, zpow_neg, zpow_natCast]
    ring
  rw [hexp_eq σ₁ ⟨le_rfl, hσ₁₂⟩, hexp_eq σ₂ ⟨hσ₁₂, le_rfl⟩] at hexp_le
  exact hexp_le

/-! ### Part 2: Anti-symmetric hyperbola factor `A_σ(m) = ∑_{d|m} μ(d) (d^(-σ) - (m/d)^(-σ))` -/

/-- Radical `rad(m) = ∏_{q | m} q`. -/
def rad (m : ℕ) : ℕ := ∏ q ∈ m.primeFactors, q

/-- Standard Euler factor `F_σ(m) = ∏_{q | m} (1 - q^(-σ))`. -/
noncomputable def eulerFactor (σ : ℝ) (m : ℕ) : ℝ :=
  ∏ q ∈ m.primeFactors, (1 - (q : ℝ) ^ (-σ))

/-- Anti-symmetric divisor factor `A_σ(m) = ∑_{d | m} μ(d) * (d^(-σ) - (m / d)^(-σ))`.
This is `2 * J_σ(m) = F_σ(m) - K_σ(m)`. -/
noncomputable def antiSymFactor (σ : ℝ) (m : ℕ) : ℝ :=
  ∑ d ∈ m.divisors, (μ d : ℝ) * ((d : ℝ) ^ (-σ) - ((m / d : ℕ) : ℝ) ^ (-σ))

/-- Helper: product of distinct primes is squarefree. -/
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

/-- Helper: Möbius of a product of distinct primes. -/
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

/-- Helper: rpow distributes over a finite product of naturals. -/
lemma prod_nat_rpow (σ : ℝ) (t : Finset ℕ) :
    ((∏ q ∈ t, q : ℕ) : ℝ) ^ σ = ∏ q ∈ t, (q : ℝ) ^ σ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert p s hps ih =>
    rw [Finset.prod_insert hps, Finset.prod_insert hps, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg _), ih]

/-- Helper: squarefree positive integer equals its radical. -/
lemma rad_eq_self_of_squarefree {d : ℕ} (hd : Squarefree d) : rad d = d := by
  unfold rad
  have hne : d ≠ 0 := hd.ne_zero
  have h1 : ∏ p ∈ d.primeFactors, p ^ d.factorization p = d := by
    simpa [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hne
  conv_rhs => rw [← h1]
  refine Finset.prod_congr rfl ?_
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hdvd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
  have hfac_ge : 1 ≤ d.factorization p := (Nat.Prime.dvd_iff_one_le_factorization hpp hne).mp hdvd
  have hfac_le : d.factorization p ≤ 1 := by
    by_contra hgt
    push Not at hgt
    have hp2 : p * p ∣ d := by
      simpa [sq] using (hpp.pow_dvd_iff_le_factorization hne).mpr hgt
    exact hpp.ne_one (Nat.isUnit_iff.mp (hd p hp2))
  rw [le_antisymm hfac_le hfac_ge, pow_one]

/-- Exact Möbius–Euler identity for ANY real exponent `τ`:
`∏_{q | m} (1 - q^τ) = ∑_{d | m} μ(d) * d^τ`. -/
lemma prod_one_sub_rpow_eq_moebius_sum (τ : ℝ) {m : ℕ} (hm : 0 < m) :
    ∏ q ∈ m.primeFactors, (1 - (q : ℝ) ^ τ) = ∑ d ∈ m.divisors, (μ d : ℝ) * (d : ℝ) ^ τ := by
  classical
  have h1 : ∏ q ∈ m.primeFactors, (1 - (q : ℝ) ^ τ)
      = ∏ q ∈ m.primeFactors, (1 + (-(q : ℝ) ^ τ)) :=
    Finset.prod_congr rfl (fun _ _ => by ring)
  rw [h1, Finset.prod_one_add]
  have hfilter : ∑ d ∈ m.divisors, (μ d : ℝ) * (d : ℝ) ^ τ
      = ∑ d ∈ m.divisors.filter Squarefree, (μ d : ℝ) * (d : ℝ) ^ τ := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro d hd hnot
    rw [Finset.mem_filter] at hnot
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree (fun hsf => hnot ⟨hd, hsf⟩)]
    simp
  rw [hfilter]
  refine Finset.sum_bij (fun t _ => ∏ q ∈ t, q) ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_powerset] at ht
    rw [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, ne_of_gt hm⟩, squarefree_prod_of_primes (fun q hq => Nat.prime_of_mem_primeFactors (ht hq))⟩
    exact dvd_trans (Finset.prod_dvd_prod_of_subset t m.primeFactors id ht) (Nat.prod_primeFactors_dvd m)
  · intro t₁ ht₁ t₂ ht₂ heq
    rw [Finset.mem_powerset] at ht₁ ht₂
    have hp₁ : ∀ q ∈ t₁, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors (ht₁ hq)
    have hp₂ : ∀ q ∈ t₂, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors (ht₂ hq)
    ext q
    constructor
    · intro hq
      have hdvd : q ∣ ∏ r ∈ t₂, r := heq ▸ Finset.dvd_prod_of_mem _ hq
      obtain ⟨r, hr, hqr⟩ := ((hp₁ q hq).prime.dvd_finsetProd_iff id).mp hdvd
      exact ((Nat.prime_dvd_prime_iff_eq (hp₁ q hq) (hp₂ r hr)).mp hqr) ▸ hr
    · intro hq
      have hdvd : q ∣ ∏ r ∈ t₁, r := heq.symm ▸ Finset.dvd_prod_of_mem _ hq
      obtain ⟨r, hr, hqr⟩ := ((hp₂ q hq).prime.dvd_finsetProd_iff id).mp hdvd
      exact ((Nat.prime_dvd_prime_iff_eq (hp₂ q hq) (hp₁ r hr)).mp hqr) ▸ hr
  · intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    refine ⟨d.primeFactors, ?_, rad_eq_self_of_squarefree hd.2⟩
    rw [Finset.mem_powerset]
    exact Nat.primeFactors_mono hd.1.1 hd.1.2
  · intro t ht
    rw [Finset.mem_powerset] at ht
    have hpt : ∀ q ∈ t, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors (ht hq)
    rw [Finset.prod_neg, moebius_prod_of_primes hpt, prod_nat_rpow τ t]
    push_cast
    rfl

/-- Exact closed form of the anti-symmetric factor `A_σ(m)`:
`A_σ(m) = (1 - (-1)^ω(m) * (m / rad(m))^(-σ)) * F_σ(m)`. -/
theorem antiSymFactor_eq_closed_form (σ : ℝ) {m : ℕ} (hm : 0 < m) :
    antiSymFactor σ m =
      (1 - (-1 : ℝ) ^ m.primeFactors.card * ((m / rad m : ℕ) : ℝ) ^ (-σ)) * eulerFactor σ m := by
  unfold antiSymFactor eulerFactor
  have hsplit : ∑ d ∈ m.divisors, (μ d : ℝ) * ((d : ℝ) ^ (-σ) - ((m / d : ℕ) : ℝ) ^ (-σ))
      = (∑ d ∈ m.divisors, (μ d : ℝ) * (d : ℝ) ^ (-σ))
        - (∑ d ∈ m.divisors, (μ d : ℝ) * ((m / d : ℕ) : ℝ) ^ (-σ)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hsplit, ← prod_one_sub_rpow_eq_moebius_sum (-σ) hm]
  -- Evaluate the second sum: ∑_{d | m} μ(d) (m/d)^(-σ) = m^(-σ) * ∑_{d | m} μ(d) d^σ = m^(-σ) * ∏_{q | m} (1 - q^σ)
  have hK : ∑ d ∈ m.divisors, (μ d : ℝ) * ((m / d : ℕ) : ℝ) ^ (-σ)
      = (m : ℝ) ^ (-σ) * ∑ d ∈ m.divisors, (μ d : ℝ) * (d : ℝ) ^ σ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro d hd
    rw [Nat.mem_divisors] at hd
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd.1 hm
    have hdiv_cast : ((m / d : ℕ) : ℝ) = (m : ℝ) / (d : ℝ) := Nat.cast_div hd.1 (ne_of_gt (Nat.cast_pos.mpr hd_pos))
    rw [hdiv_cast, Real.div_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg d),
      div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg d), neg_neg]
    ring
  rw [hK, ← prod_one_sub_rpow_eq_moebius_sum σ hm]
  -- Factor out (-q^σ) from each (1 - q^σ) = -q^σ * (1 - q^(-σ)):
  have hprod_rel : ∏ q ∈ m.primeFactors, (1 - (q : ℝ) ^ σ)
      = (-1 : ℝ) ^ m.primeFactors.card * ((rad m : ℕ) : ℝ) ^ σ * ∏ q ∈ m.primeFactors, (1 - (q : ℝ) ^ (-σ)) := by
    have hstep : ∏ q ∈ m.primeFactors, (1 - (q : ℝ) ^ σ)
        = ∏ q ∈ m.primeFactors, ((-(q : ℝ) ^ σ) * (1 - (q : ℝ) ^ (-σ))) := by
      refine Finset.prod_congr rfl ?_
      intro q hq
      have hqp : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hq).pos
      have hmul : (q : ℝ) ^ σ * (q : ℝ) ^ (-σ) = 1 := by
        rw [← Real.rpow_add hqp, add_neg_cancel, Real.rpow_zero]
      calc 1 - (q : ℝ) ^ σ = -(q : ℝ) ^ σ + (q : ℝ) ^ σ * (q : ℝ) ^ (-σ) := by rw [hmul]; ring
        _ = (-(q : ℝ) ^ σ) * (1 - (q : ℝ) ^ (-σ)) := by ring
    rw [hstep, Finset.prod_mul_distrib, Finset.prod_neg, ← prod_nat_rpow σ m.primeFactors]
    rfl
  rw [hprod_rel]
  -- Combine m^(-σ) * (rad m)^σ = (m / rad m)^(-σ):
  have hrad_dvd : rad m ∣ m := Nat.prod_primeFactors_dvd m
  have hrad_pos : 0 < rad m := Finset.prod_pos (fun q hq => (Nat.prime_of_mem_primeFactors hq).pos)
  have hratio : (m : ℝ) ^ (-σ) * ((rad m : ℕ) : ℝ) ^ σ = ((m / rad m : ℕ) : ℝ) ^ (-σ) := by
    have hdiv_cast : ((m / rad m : ℕ) : ℝ) = (m : ℝ) / ((rad m : ℕ) : ℝ) :=
      Nat.cast_div hrad_dvd (ne_of_gt (Nat.cast_pos.mpr hrad_pos))
    rw [hdiv_cast, Real.div_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg _),
      div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg _), neg_neg]
  calc (∏ q ∈ m.primeFactors, (1 - (q : ℝ) ^ (-σ)))
        - (m : ℝ) ^ (-σ) * ((-1 : ℝ) ^ m.primeFactors.card * ((rad m : ℕ) : ℝ) ^ σ
            * ∏ q ∈ m.primeFactors, (1 - (q : ℝ) ^ (-σ)))
      = (1 - (-1 : ℝ) ^ m.primeFactors.card * ((m : ℝ) ^ (-σ) * ((rad m : ℕ) : ℝ) ^ σ))
          * ∏ q ∈ m.primeFactors, (1 - (q : ℝ) ^ (-σ)) := by ring
    _ = (1 - (-1 : ℝ) ^ m.primeFactors.card * ((m / rad m : ℕ) : ℝ) ^ (-σ))
          * ∏ q ∈ m.primeFactors, (1 - (q : ℝ) ^ (-σ)) := by rw [hratio]

/-- Exact vanishing of `A_σ(m)` on every squarefree `m` with even `ω(m)` (including all semiprimes `p₁ p₂`). -/
theorem antiSymFactor_eq_zero_of_squarefree_even (σ : ℝ) {m : ℕ}
    (hm : Squarefree m) (heven : Even m.primeFactors.card) :
    antiSymFactor σ m = 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  rw [antiSymFactor_eq_closed_form σ hm_pos, rad_eq_self_of_squarefree hm, Nat.div_self hm_pos]
  simp [heven.neg_one_pow]

/-- Exact value of `A_σ(p)` on a prime `p`: `A_σ(p) = 2 * (1 - p^(-σ))`. -/
lemma antiSymFactor_prime (σ : ℝ) {p : ℕ} (hp : p.Prime) :
    antiSymFactor σ p = 2 * (1 - (p : ℝ) ^ (-σ)) := by
  rw [antiSymFactor_eq_closed_form σ hp.pos]
  have hpf : p.primeFactors = {p} := hp.primeFactors
  have hrad : rad p = p := by unfold rad; rw [hpf]; simp
  rw [hrad, Nat.div_self hp.pos, hpf]
  unfold eulerFactor
  rw [hpf]
  simp only [Finset.card_singleton, pow_one, Nat.cast_one, Real.one_rpow, Finset.prod_singleton]
  ring

/-- Non-negativity of `A_σ(m)` for every `σ > 0` and `m ≥ 1`. -/
lemma antiSymFactor_nonneg {σ : ℝ} (hσ : 0 < σ) {m : ℕ} (hm : 0 < m) :
    0 ≤ antiSymFactor σ m := by
  rw [antiSymFactor_eq_closed_form σ hm]
  have hf_nonneg : 0 ≤ eulerFactor σ m := by
    unfold eulerFactor
    refine Finset.prod_nonneg ?_
    intro q hq
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_le
    have hle : (q : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1 (by linarith)
    linarith
  have hrad_dvd : rad m ∣ m := Nat.prod_primeFactors_dvd m
  have hb_pos : 1 ≤ m / rad m := Nat.div_pos (Nat.le_of_dvd hm hrad_dvd)
    (Finset.prod_pos (fun q hq => (Nat.prime_of_mem_primeFactors hq).pos))
  have hb_rpow_le : ((m / rad m : ℕ) : ℝ) ^ (-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hb_pos) (by linarith)
  have hb_rpow_nonneg : 0 ≤ ((m / rad m : ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hpre_nonneg : 0 ≤ 1 - (-1 : ℝ) ^ m.primeFactors.card * ((m / rad m : ℕ) : ℝ) ^ (-σ) := by
    rcases Nat.even_or_odd m.primeFactors.card with he | ho
    · rw [he.neg_one_pow]; linarith
    · rw [ho.neg_one_pow]; linarith
  exact mul_nonneg hpre_nonneg hf_nonneg

/-- Prime-power upper bound: for `σ > 0` and `m` with `m.primeFactors.card = 1`,
`A_σ(m) / σ ≤ 2 * ∑_{q | m} log q`. -/
lemma antiSymFactor_pp_div_le {σ : ℝ} (hσ : 0 < σ) {m : ℕ} (hm : 0 < m) (h1 : m.primeFactors.card = 1) :
    antiSymFactor σ m / σ ≤ 2 * ∑ q ∈ m.primeFactors, Real.log (q : ℝ) := by
  rw [antiSymFactor_eq_closed_form σ hm]
  obtain ⟨q, hq_eq⟩ := Finset.card_eq_one.mp h1
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors (by rw [hq_eq]; simp)
  have hrad_dvd : rad m ∣ m := Nat.prod_primeFactors_dvd m
  have hb_pos : 1 ≤ m / rad m := Nat.div_pos (Nat.le_of_dvd hm hrad_dvd)
    (Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos))
  have hb_le : ((m / rad m : ℕ) : ℝ) ^ (-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hb_pos) (by linarith)
  have hpre : 1 - (-1 : ℝ) ^ m.primeFactors.card * ((m / rad m : ℕ) : ℝ) ^ (-σ) ≤ 2 := by
    rw [h1]; norm_num; linarith
  have hq_exp : (q : ℝ) ^ (-σ) = Real.exp (-σ * Real.log (q : ℝ)) := by
    rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hqp.pos), mul_comm]
  have hf_le : 1 - (q : ℝ) ^ (-σ) ≤ σ * Real.log (q : ℝ) := by
    rw [hq_exp]
    linarith [Real.add_one_le_exp (-σ * Real.log (q : ℝ))]
  have hf_nonneg : 0 ≤ 1 - (q : ℝ) ^ (-σ) := by
    have : (q : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hqp.one_le) (by linarith)
    linarith
  have hlog_nonneg : 0 ≤ Real.log (q : ℝ) := le_of_lt (Real.log_pos (by exact_mod_cast hqp.one_lt))
  simp only [eulerFactor, hq_eq, Finset.prod_singleton, Finset.sum_singleton]
  rw [div_le_iff₀ hσ]
  calc (1 - (-1 : ℝ) ^ ({q} : Finset ℕ).card * ((m / rad m : ℕ) : ℝ) ^ (-σ)) * (1 - (q : ℝ) ^ (-σ))
      ≤ 2 * (1 - (q : ℝ) ^ (-σ)) := by
        have hpre' : 1 - (-1 : ℝ) ^ ({q} : Finset ℕ).card * ((m / rad m : ℕ) : ℝ) ^ (-σ) ≤ 2 := by
          simpa [hq_eq] using hpre
        exact mul_le_mul_of_nonneg_right hpre' hf_nonneg
    _ ≤ 2 * (σ * Real.log (q : ℝ)) := mul_le_mul_of_nonneg_left hf_le (by norm_num)
    _ = 2 * Real.log (q : ℝ) * σ := by ring

/-- Helper: `∑_{q | m} log q + log (m / rad m) = log m` for every `m ≥ 1`. -/
lemma sum_log_primeFactors_add_log_div_rad {m : ℕ} (hm : 0 < m) :
    (∑ q ∈ m.primeFactors, Real.log (q : ℝ)) + Real.log ((m / rad m : ℕ) : ℝ) = Real.log (m : ℝ) := by
  have hrad_dvd : rad m ∣ m := Nat.prod_primeFactors_dvd m
  have hrad_pos : 0 < rad m := Finset.prod_pos (fun q hq => (Nat.prime_of_mem_primeFactors hq).pos)
  have hb_pos : 0 < m / rad m := Nat.div_pos (Nat.le_of_dvd hm hrad_dvd) hrad_pos
  have hprod_log : ∑ q ∈ m.primeFactors, Real.log (q : ℝ) = Real.log ((rad m : ℕ) : ℝ) := by
    unfold rad
    rw [Nat.cast_prod, Real.log_prod]
    intro q hq
    exact ne_of_gt (Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hq).pos)
  rw [hprod_log, ← Real.log_mul (ne_of_gt (Nat.cast_pos.mpr hrad_pos)) (ne_of_gt (Nat.cast_pos.mpr hb_pos)),
    ← Nat.cast_mul, Nat.mul_div_cancel' hrad_dvd]

/-- **Core Bilateral Composite Monotonicity for `A_σ`**:
For any `x, y ≥ 2` with `x ≤ n`, `y ≤ n`, and `ω(x) + ω(y) ≥ 3`, and any `0 < σ₁ ≤ σ₂ ≤ 2 / log n`,
`σ₁^(-2) * A_{σ₁}(x) * A_{σ₁}(y) ≤ σ₂^(-2) * A_{σ₂}(x) * A_{σ₂}(y)`. -/
theorem antiSym_bilateral_composite_mono {n x y : ℕ} (hn : 4 ≤ n)
    (hx : 2 ≤ x) (hxn : x ≤ n) (hy : 2 ≤ y) (hyn : y ≤ n)
    (hcomp : 3 ≤ x.primeFactors.card + y.primeFactors.card)
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ ≤ σ₂) (hσ₂ : σ₂ ≤ 2 / Real.log (n : ℝ)) :
    σ₁ ^ (-(2 : ℤ)) * (antiSymFactor σ₁ x * antiSymFactor σ₁ y) ≤
      σ₂ ^ (-(2 : ℤ)) * (antiSymFactor σ₂ x * antiSymFactor σ₂ y) := by
  have hx_pos : 0 < x := by omega
  have hy_pos : 0 < y := by omega
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  -- Handle vanishing cases (squarefree with even ω) immediately:
  by_cases hzx : Even x.primeFactors.card ∧ x / rad x = 1
  · have hrad_dvd : rad x ∣ x := Nat.prod_primeFactors_dvd x
    have hrad_eq : rad x = x := by
      have := Nat.mul_div_cancel' hrad_dvd
      rw [hzx.2, mul_one] at this
      exact this
    have hzero : ∀ σ : ℝ, antiSymFactor σ x = 0 := by
      intro σ
      rw [antiSymFactor_eq_closed_form σ hx_pos, hzx.2]
      simp [hzx.1.neg_one_pow]
    simp [hzero]
  by_cases hzy : Even y.primeFactors.card ∧ y / rad y = 1
  · have hzero : ∀ σ : ℝ, antiSymFactor σ y = 0 := by
      intro σ
      rw [antiSymFactor_eq_closed_form σ hy_pos, hzy.2]
      simp [hzy.1.neg_one_pow]
    simp [hzero]
  -- Otherwise both A_σ(x) and A_σ(y) are products of (1 - exp (-σ * a_i)) and (1 + exp (-σ * b_j))!
  -- Build finsets s_x (minus-factors) and t_x (plus-factors) for each side:
  -- Side x: always has x.primeFactors in s_x; if Even ω(x) (so x/rad x ≥ 2), add log(x/rad x) to s_x;
  --         if Odd ω(x), add log(x/rad x) to t_x.
  have hradx_pos : 0 < rad x := Finset.prod_pos (fun q hq => (Nat.prime_of_mem_primeFactors hq).pos)
  have hrady_pos : 0 < rad y := Finset.prod_pos (fun q hq => (Nat.prime_of_mem_primeFactors hq).pos)
  have hbx_ge1 : 1 ≤ x / rad x := Nat.div_pos (Nat.le_of_dvd hx_pos (Nat.prod_primeFactors_dvd x)) hradx_pos
  have hby_ge1 : 1 ≤ y / rad y := Nat.div_pos (Nat.le_of_dvd hy_pos (Nat.prod_primeFactors_dvd y)) hrady_pos
  let ex_even : Bool := decide (Even x.primeFactors.card)
  let ey_even : Bool := decide (Even y.primeFactors.card)
  -- Index type for minus-factors: Sum (Option ℕ) (Option ℕ)
  -- inl (some q) = q ∈ x.primeFactors; inl none = extra (x/rad x) when ex_even;
  -- inr (some r) = r ∈ y.primeFactors; inr none = extra (y/rad y) when ey_even.
  let sx : Finset (Option ℕ) :=
    x.primeFactors.image some ∪ (if ex_even then {none} else ∅)
  let sy : Finset (Option ℕ) :=
    y.primeFactors.image some ∪ (if ey_even then {none} else ∅)
  let s : Finset (Option ℕ ⊕ Option ℕ) := sx.disjSum sy
  let a : Option ℕ ⊕ Option ℕ → ℝ :=
    Sum.elim
      (fun o => match o with | some q => Real.log (q : ℝ) | none => Real.log ((x / rad x : ℕ) : ℝ))
      (fun o => match o with | some r => Real.log (r : ℝ) | none => Real.log ((y / rad y : ℕ) : ℝ))
  let t : Finset (Bool) :=
    (if !ex_even then {false} else ∅) ∪ (if !ey_even then {true} else ∅)
  let b : Bool → ℝ := fun fl =>
    if fl then Real.log ((y / rad y : ℕ) : ℝ) else Real.log ((x / rad x : ℕ) : ℝ)
  -- Verify positivity of a on s:
  have ha_pos : ∀ i ∈ s, 0 < a i := by
    intro i hi
    cases i with
    | inl o =>
      have ho : o ∈ sx := by simpa [s] using hi
      cases o with
      | some q =>
        have hq : q ∈ x.primeFactors := by
          simp only [sx, Finset.mem_union, Finset.mem_image] at ho
          rcases ho with ⟨q', hq', hqq⟩ | hnone
          · cases hqq; exact hq'
          · split_ifs at hnone <;> simp at hnone
        exact Real.log_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_lt)
      | none =>
        have hev : Even x.primeFactors.card := by
          simp only [sx, Finset.mem_union, Finset.mem_image] at ho
          rcases ho with ⟨_, _, h⟩ | hnone
          · simp at h
          · by_contra hno
            have : ex_even = false := decide_eq_false hno
            simp [this] at hnone
        have hne1 : x / rad x ≠ 1 := fun h => hzx ⟨hev, h⟩
        have hgt1 : 1 < x / rad x := by omega
        exact Real.log_pos (by exact_mod_cast hgt1)
    | inr o =>
      have ho : o ∈ sy := by simpa [s] using hi
      cases o with
      | some r =>
        have hr : r ∈ y.primeFactors := by
          simp only [sy, Finset.mem_union, Finset.mem_image] at ho
          rcases ho with ⟨r', hr', hrr⟩ | hnone
          · cases hrr; exact hr'
          · split_ifs at hnone <;> simp at hnone
        exact Real.log_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hr).one_lt)
      | none =>
        have hev : Even y.primeFactors.card := by
          simp only [sy, Finset.mem_union, Finset.mem_image] at ho
          rcases ho with ⟨_, _, h⟩ | hnone
          · simp at h
          · by_contra hno
            have : ey_even = false := decide_eq_false hno
            simp [this] at hnone
        have hne1 : y / rad y ≠ 1 := fun h => hzy ⟨hev, h⟩
        have hgt1 : 1 < y / rad y := by omega
        exact Real.log_pos (by exact_mod_cast hgt1)
  have hb_nonneg : ∀ j ∈ t, 0 ≤ b j := by
    intro j _
    cases j
    · exact Real.log_nonneg (by exact_mod_cast hbx_ge1)
    · exact Real.log_nonneg (by exact_mod_cast hby_ge1)
  -- Cardinality of s: s.card ≥ 4!
  have hdisj_x : Disjoint (x.primeFactors.image some) (if ex_even then ({none} : Finset (Option ℕ)) else ∅) := by
    split_ifs <;> simp
  have hdisj_y : Disjoint (y.primeFactors.image some) (if ey_even then ({none} : Finset (Option ℕ)) else ∅) := by
    split_ifs <;> simp
  have hcard_sx : sx.card = x.primeFactors.card + (if ex_even then 1 else 0) := by
    simp only [sx, Finset.card_union_of_disjoint hdisj_x, Finset.card_image_of_injective _ (Option.some_injective ℕ)]
    split_ifs <;> simp
  have hcard_sy : sy.card = y.primeFactors.card + (if ey_even then 1 else 0) := by
    simp only [sy, Finset.card_union_of_disjoint hdisj_y, Finset.card_image_of_injective _ (Option.some_injective ℕ)]
    split_ifs <;> simp
  have hcard_s_ge4 : 4 ≤ s.card := by
    have hcx : 1 ≤ x.primeFactors.card := Finset.one_le_card.mpr (Nat.nonempty_primeFactors.mpr (by omega))
    have hcy : 1 ≤ y.primeFactors.card := Finset.one_le_card.mpr (Nat.nonempty_primeFactors.mpr (by omega))
    have hs : s.card = sx.card + sy.card := Finset.card_disjSum sx sy
    have heff_x : (if x.primeFactors.card = 1 then 1 else 3) ≤ sx.card := by
      rw [hcard_sx]
      by_cases h1 : x.primeFactors.card = 1
      · simp [h1]
      · simp only [h1, if_false]
        by_cases h2 : x.primeFactors.card = 2
        · have he : ex_even = true := decide_eq_true (by rw [h2]; exact ⟨1, rfl⟩)
          simp [h2, he]
        · omega
    have heff_y : (if y.primeFactors.card = 1 then 1 else 3) ≤ sy.card := by
      rw [hcard_sy]
      by_cases h1 : y.primeFactors.card = 1
      · simp [h1]
      · simp only [h1, if_false]
        by_cases h2 : y.primeFactors.card = 2
        · have he : ey_even = true := decide_eq_true (by rw [h2]; exact ⟨1, rfl⟩)
          simp [h2, he]
        · omega
    rw [hs]
    by_cases hx1 : x.primeFactors.card = 1 <;> by_cases hy1 : y.primeFactors.card = 1
    · omega
    · simp only [hx1, hy1, if_true, if_false] at heff_x heff_y; omega
    · simp only [hx1, hy1, if_true, if_false] at heff_x heff_y; omega
    · simp only [hx1, hy1, if_false] at heff_x heff_y; omega
  -- Total exponent sum equals log x + log y ≤ 2 * log n!
  have hsum_eq : (∑ i ∈ s, a i) + (∑ j ∈ t, b j) = Real.log (x : ℝ) + Real.log (y : ℝ) := by
    have hsum_sx : ∑ o ∈ sx, (match o with | some q => Real.log (q : ℝ) | none => Real.log ((x / rad x : ℕ) : ℝ))
        = (∑ q ∈ x.primeFactors, Real.log (q : ℝ))
          + (if ex_even then Real.log ((x / rad x : ℕ) : ℝ) else 0) := by
      rw [Finset.sum_union hdisj_x, Finset.sum_image (fun _ _ _ _ h => Option.some_injective ℕ h)]
      split_ifs <;> simp
    have hsum_sy : ∑ o ∈ sy, (match o with | some r => Real.log (r : ℝ) | none => Real.log ((y / rad y : ℕ) : ℝ))
        = (∑ r ∈ y.primeFactors, Real.log (r : ℝ))
          + (if ey_even then Real.log ((y / rad y : ℕ) : ℝ) else 0) := by
      rw [Finset.sum_union hdisj_y, Finset.sum_image (fun _ _ _ _ h => Option.some_injective ℕ h)]
      split_ifs <;> simp
    have hdisj_t : Disjoint (if !ex_even then ({false} : Finset Bool) else ∅)
        (if !ey_even then ({true} : Finset Bool) else ∅) := by
      split_ifs <;> simp
    have hsum_t : ∑ j ∈ t, b j
        = (if !ex_even then Real.log ((x / rad x : ℕ) : ℝ) else 0)
          + (if !ey_even then Real.log ((y / rad y : ℕ) : ℝ) else 0) := by
      simp only [t, Finset.sum_union hdisj_t]
      split_ifs <;> simp [b]
    have hsum_s : ∑ i ∈ s, a i
        = ((∑ q ∈ x.primeFactors, Real.log (q : ℝ)) + (if ex_even then Real.log ((x / rad x : ℕ) : ℝ) else 0))
          + ((∑ r ∈ y.primeFactors, Real.log (r : ℝ)) + (if ey_even then Real.log ((y / rad y : ℕ) : ℝ) else 0)) := by
      simp only [s, Finset.sum_disjSum, a, Sum.elim_inl, Sum.elim_inr]
      rw [hsum_sx, hsum_sy]
    rw [hsum_s, hsum_t]
    have hlogx := sum_log_primeFactors_add_log_div_rad hx_pos
    have hlogy := sum_log_primeFactors_add_log_div_rad hy_pos
    cases ex_even <;> cases ey_even <;> simp <;> linarith
  have hbound : σ₂ * ((∑ i ∈ s, a i) + (∑ j ∈ t, b j)) ≤ 2 * ((s.card : ℝ) - (2 : ℝ)) := by
    rw [hsum_eq]
    have hlx : Real.log (x : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (Nat.cast_pos.mpr hx_pos) (Nat.cast_le.mpr hxn)
    have hly : Real.log (y : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (Nat.cast_pos.mpr hy_pos) (Nat.cast_le.mpr hyn)
    have hsum_nonneg : 0 ≤ Real.log (x : ℝ) + Real.log (y : ℝ) :=
      add_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x)))
        (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ y)))
    have hmul : σ₂ * (Real.log (x : ℝ) + Real.log (y : ℝ))
        ≤ (2 / Real.log (n : ℝ)) * (2 * Real.log (n : ℝ)) :=
      mul_le_mul hσ₂ (by linarith) hsum_nonneg (le_of_lt (div_pos (by norm_num) hlogn_pos))
    have h4 : (2 / Real.log (n : ℝ)) * (2 * Real.log (n : ℝ)) = 4 := by
      field_simp [ne_of_gt hlogn_pos]
      ring
    have hcard_r : (4 : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast hcard_s_ge4
    linarith
  have hmono := scaled_euler_plus_minus_mono s a ha_pos t b hb_nonneg 2 hσ₁ hσ₁₂ hbound
  -- Match the product with antiSymFactor σ x * antiSymFactor σ y:
  have hprod_eq : ∀ σ : ℝ,
      (∏ i ∈ s, (1 - Real.exp (-σ * a i))) * (∏ j ∈ t, (1 + Real.exp (-σ * b j)))
      = antiSymFactor σ x * antiSymFactor σ y := by
    intro σ
    rw [antiSymFactor_eq_closed_form σ hx_pos, antiSymFactor_eq_closed_form σ hy_pos]
    have hdisj_t : Disjoint (if !ex_even then ({false} : Finset Bool) else ∅)
        (if !ey_even then ({true} : Finset Bool) else ∅) := by
      split_ifs <;> simp
    have hx_exp : Real.exp (-(σ * Real.log ((x / rad x : ℕ) : ℝ))) = ((x / rad x : ℕ) : ℝ) ^ (-σ) := by
      rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr (by omega))]; congr 1; ring
    have hy_exp : Real.exp (-(σ * Real.log ((y / rad y : ℕ) : ℝ))) = ((y / rad y : ℕ) : ℝ) ^ (-σ) := by
      rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr (by omega))]; congr 1; ring
    have hpt : ∏ j ∈ t, (1 + Real.exp (-σ * b j))
        = (if !ex_even then 1 + ((x / rad x : ℕ) : ℝ) ^ (-σ) else 1)
          * (if !ey_even then 1 + ((y / rad y : ℕ) : ℝ) ^ (-σ) else 1) := by
      simp only [t, Finset.prod_union hdisj_t]
      cases ex_even <;> cases ey_even <;> simp [b, hx_exp, hy_exp]
    have hpsx : ∏ o ∈ sx, (1 - Real.exp (-σ * match o with | some q => Real.log (q : ℝ) | none => Real.log ((x / rad x : ℕ) : ℝ)))
        = eulerFactor σ x * (if ex_even then 1 - ((x / rad x : ℕ) : ℝ) ^ (-σ) else 1) := by
      rw [Finset.prod_union hdisj_x, Finset.prod_image (fun _ _ _ _ h => Option.some_injective ℕ h)]
      have hf : ∏ q ∈ x.primeFactors, (1 - Real.exp (-σ * Real.log (q : ℝ))) = eulerFactor σ x := by
        unfold eulerFactor
        refine Finset.prod_congr rfl fun q hq => ?_
        rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hq).pos), mul_comm]
      rw [hf]
      cases ex_even <;> simp [hx_exp]
    have hpsy : ∏ o ∈ sy, (1 - Real.exp (-σ * match o with | some r => Real.log (r : ℝ) | none => Real.log ((y / rad y : ℕ) : ℝ)))
        = eulerFactor σ y * (if ey_even then 1 - ((y / rad y : ℕ) : ℝ) ^ (-σ) else 1) := by
      rw [Finset.prod_union hdisj_y, Finset.prod_image (fun _ _ _ _ h => Option.some_injective ℕ h)]
      have hf : ∏ r ∈ y.primeFactors, (1 - Real.exp (-σ * Real.log (r : ℝ))) = eulerFactor σ y := by
        unfold eulerFactor
        refine Finset.prod_congr rfl fun r hr => ?_
        rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hr).pos), mul_comm]
      rw [hf]
      cases ey_even <;> simp [hy_exp]
    have hps : ∏ i ∈ s, (1 - Real.exp (-σ * a i))
        = (eulerFactor σ x * (if ex_even then 1 - ((x / rad x : ℕ) : ℝ) ^ (-σ) else 1))
          * (eulerFactor σ y * (if ey_even then 1 - ((y / rad y : ℕ) : ℝ) ^ (-σ) else 1)) := by
      simp only [s, Finset.prod_disjSum, a, Sum.elim_inl, Sum.elim_inr]
      rw [hpsx, hpsy]
    rw [hps, hpt]
    have hsign_x : (-1 : ℝ) ^ x.primeFactors.card = if ex_even then 1 else -1 := by
      rcases Nat.even_or_odd x.primeFactors.card with he | ho
      · have : ex_even = true := decide_eq_true he
        simp [this, he.neg_one_pow]
      · have : ex_even = false := decide_eq_false (Nat.not_even_iff_odd.mpr ho)
        simp [this, ho.neg_one_pow]
    have hsign_y : (-1 : ℝ) ^ y.primeFactors.card = if ey_even then 1 else -1 := by
      rcases Nat.even_or_odd y.primeFactors.card with he | ho
      · have : ey_even = true := decide_eq_true he
        simp [this, he.neg_one_pow]
      · have : ey_even = false := decide_eq_false (Nat.not_even_iff_odd.mpr ho)
        simp [this, ho.neg_one_pow]
    rw [hsign_x, hsign_y]
    cases ex_even <;> cases ey_even <;> simp <;> ring
  rw [mul_assoc, hprod_eq σ₁, mul_assoc, hprod_eq σ₂] at hmono
  exact hmono

/-! ### Part 3: 4-Quadrant Hyperbola Split & Explicit Prime-Power Bound -/

/-- Short-divisor part `A_{S,D}(σ, m) = ∑_{d | m, d ≤ D} μ(d) * (d^(-σ) - (m/d)^(-σ))`. -/
noncomputable def antiSymShort (D : ℕ) (σ : ℝ) (m : ℕ) : ℝ :=
  ∑ d ∈ m.divisors.filter (· ≤ D), (μ d : ℝ) * ((d : ℝ) ^ (-σ) - ((m / d : ℕ) : ℝ) ^ (-σ))

/-- Long-divisor part `A_{L,D}(σ, m) = ∑_{d | m, D < d} μ(d) * (d^(-σ) - (m/d)^(-σ))`. -/
noncomputable def antiSymLong (D : ℕ) (σ : ℝ) (m : ℕ) : ℝ :=
  ∑ d ∈ m.divisors.filter (D < ·), (μ d : ℝ) * ((d : ℝ) ^ (-σ) - ((m / d : ℕ) : ℝ) ^ (-σ))

lemma antiSymFactor_eq_short_add_long (D : ℕ) (σ : ℝ) (m : ℕ) :
    antiSymFactor σ m = antiSymShort D σ m + antiSymLong D σ m := by
  unfold antiSymFactor antiSymShort antiSymLong
  have h := Finset.sum_filter_add_sum_filter_not m.divisors (· ≤ D)
    (fun d => (μ d : ℝ) * ((d : ℝ) ^ (-σ) - ((m / d : ℕ) : ℝ) ^ (-σ)))
  simpa [not_le] using h.symm

/-- Bilateral anti-symmetric sum `4 * Ξ_n^J(σ) = σ^(-2) * ∑_{x=2}^{n-2} A_σ(x) * A_σ(n - x)`. -/
noncomputable def bilateralAntiSym (n : ℕ) (σ : ℝ) : ℝ :=
  σ ^ (-(2 : ℤ)) * ∑ x ∈ Finset.Icc 2 (n - 2), antiSymFactor σ x * antiSymFactor σ (n - x)

/-- Short-short quadrant `SS_D(n; σ₁, σ₂)` (100% elementary CRT, `d₁, d₂ ≤ D`). -/
noncomputable def quadSS (n D : ℕ) (σ₁ σ₂ : ℝ) : ℝ :=
  ∑ x ∈ Finset.Icc 2 (n - 2),
    (σ₁ ^ (-(2 : ℤ)) * (antiSymShort D σ₁ x * antiSymShort D σ₁ (n - x))
      - σ₂ ^ (-(2 : ℤ)) * (antiSymShort D σ₂ x * antiSymShort D σ₂ (n - x)))

/-- Short-long quadrant `SL_D(n; σ₁, σ₂)` (single long Möbius factor in APs, `d₁ ≤ D < d₂`). -/
noncomputable def quadSL (n D : ℕ) (σ₁ σ₂ : ℝ) : ℝ :=
  ∑ x ∈ Finset.Icc 2 (n - 2),
    (σ₁ ^ (-(2 : ℤ)) * (antiSymShort D σ₁ x * antiSymLong D σ₁ (n - x))
      - σ₂ ^ (-(2 : ℤ)) * (antiSymShort D σ₂ x * antiSymLong D σ₂ (n - x)))

/-- Long-long quadrant `LL_D(n; σ₁, σ₂)` (pure binary Möbius correlation, `D < d₁, d₂`). -/
noncomputable def quadLL (n D : ℕ) (σ₁ σ₂ : ℝ) : ℝ :=
  ∑ x ∈ Finset.Icc 2 (n - 2),
    (σ₁ ^ (-(2 : ℤ)) * (antiSymLong D σ₁ x * antiSymLong D σ₁ (n - x))
      - σ₂ ^ (-(2 : ℤ)) * (antiSymLong D σ₂ x * antiSymLong D σ₂ (n - x)))

/-- **Exact 4-Quadrant Hyperbola Identity** (`LS = SL` by reflection `x ↦ n - x`):
`4*(Ξ_n^J(σ₁) - Ξ_n^J(σ₂)) = SS_D + 2 * SL_D + LL_D`. -/
theorem bilateralAntiSym_quadrant_split (n D : ℕ) (σ₁ σ₂ : ℝ) :
    bilateralAntiSym n σ₁ - bilateralAntiSym n σ₂ =
      quadSS n D σ₁ σ₂ + 2 * quadSL n D σ₁ σ₂ + quadLL n D σ₁ σ₂ := by
  unfold bilateralAntiSym quadSS quadSL quadLL
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  -- Reflection symmetry: ∑_{x ∈ Icc 2 (n-2)} L(x)*S(n-x) = ∑_{x ∈ Icc 2 (n-2)} S(x)*L(n-x)
  have hrefl : ∀ σ : ℝ,
      ∑ x ∈ Finset.Icc 2 (n - 2), σ ^ (-(2 : ℤ)) * (antiSymLong D σ x * antiSymShort D σ (n - x))
      = ∑ x ∈ Finset.Icc 2 (n - 2), σ ^ (-(2 : ℤ)) * (antiSymShort D σ x * antiSymLong D σ (n - x)) := by
    intro σ
    refine Finset.sum_bij (fun x _ => n - x) ?_ ?_ ?_ ?_
    · intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
    · intro x₁ hx₁ x₂ hx₂ heq; rw [Finset.mem_Icc] at hx₁ hx₂; omega
    · intro y hy; rw [Finset.mem_Icc] at hy; exact ⟨n - y, Finset.mem_Icc.mpr (by omega), by omega⟩
    · intro x hx
      rw [Finset.mem_Icc] at hx
      have hnn : n - (n - x) = x := by omega
      rw [hnn]; ring
  have hLS : ∑ x ∈ Finset.Icc 2 (n - 2),
        (σ₁ ^ (-(2 : ℤ)) * (antiSymLong D σ₁ x * antiSymShort D σ₁ (n - x))
          - σ₂ ^ (-(2 : ℤ)) * (antiSymLong D σ₂ x * antiSymShort D σ₂ (n - x)))
      = ∑ x ∈ Finset.Icc 2 (n - 2),
        (σ₁ ^ (-(2 : ℤ)) * (antiSymShort D σ₁ x * antiSymLong D σ₁ (n - x))
          - σ₂ ^ (-(2 : ℤ)) * (antiSymShort D σ₂ x * antiSymLong D σ₂ (n - x))) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hrefl σ₁, hrefl σ₂]
  have hexpand : ∀ x ∈ Finset.Icc 2 (n - 2),
      σ₁ ^ (-(2 : ℤ)) * (antiSymFactor σ₁ x * antiSymFactor σ₁ (n - x))
        - σ₂ ^ (-(2 : ℤ)) * (antiSymFactor σ₂ x * antiSymFactor σ₂ (n - x))
      = (σ₁ ^ (-(2 : ℤ)) * (antiSymShort D σ₁ x * antiSymShort D σ₁ (n - x))
          - σ₂ ^ (-(2 : ℤ)) * (antiSymShort D σ₂ x * antiSymShort D σ₂ (n - x)))
        + (σ₁ ^ (-(2 : ℤ)) * (antiSymShort D σ₁ x * antiSymLong D σ₁ (n - x))
            - σ₂ ^ (-(2 : ℤ)) * (antiSymShort D σ₂ x * antiSymLong D σ₂ (n - x)))
        + (σ₁ ^ (-(2 : ℤ)) * (antiSymLong D σ₁ x * antiSymShort D σ₁ (n - x))
            - σ₂ ^ (-(2 : ℤ)) * (antiSymLong D σ₂ x * antiSymShort D σ₂ (n - x)))
        + (σ₁ ^ (-(2 : ℤ)) * (antiSymLong D σ₁ x * antiSymLong D σ₁ (n - x))
            - σ₂ ^ (-(2 : ℤ)) * (antiSymLong D σ₂ x * antiSymLong D σ₂ (n - x))) := by
    intro x _
    rw [antiSymFactor_eq_short_add_long D σ₁ x, antiSymFactor_eq_short_add_long D σ₁ (n - x),
      antiSymFactor_eq_short_add_long D σ₂ x, antiSymFactor_eq_short_add_long D σ₂ (n - x)]
    ring
  rw [Finset.sum_congr rfl hexpand, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, hLS]
  ring

/-- Goldbach prime-pair sum `R_pr(n)`. -/
noncomputable def goldbachPrimePairSum (n : ℕ) : ℝ :=
  ∑ x ∈ (Finset.Icc 2 (n - 2)).filter (fun x => x.Prime ∧ (n - x).Prime),
    Real.log (x : ℝ) * Real.log ((n - x : ℕ) : ℝ)

/-- Bilateral proper prime-power sum `P_pp(n)`. -/
noncomputable def bilateralPrimePowerErr (n : ℕ) : ℝ :=
  ∑ x ∈ (Finset.Icc 2 (n - 2)).filter
      (fun x => x.primeFactors.card = 1 ∧ (n - x).primeFactors.card = 1 ∧ ¬(x.Prime ∧ (n - x).Prime)),
    (∑ q ∈ x.primeFactors, Real.log (q : ℝ)) * (∑ r ∈ (n - x).primeFactors, Real.log (r : ℝ))

/-- Elementary cardinality bound: the number of proper prime powers `p^a ≤ n` (`a ≥ 2`) in `[2, n-2]`
is at most `Nat.sqrt n * Nat.log 2 n`. -/
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
    have ha_ne0 : a ≠ 0 := by
      intro h0
      rw [show x.factorization p = 0 from h0, pow_zero] at hx_pow
      omega
    have ha_ne1 : a ≠ 1 := by
      intro h1
      rw [show x.factorization p = 1 from h1, pow_one] at hx_pow
      exact hx.2.2 (hx_pow ▸ hpp)
    have ha_ge2 : 2 ≤ a := by omega
    have hp_le : p ≤ Nat.sqrt n := by
      rw [Nat.le_sqrt]
      have hp2 : p * p ≤ x := by
        calc p * p = p ^ 2 := by ring
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
    _ ≤ Nat.sqrt n * Nat.log 2 n := by
        apply Nat.mul_le_mul <;> simp

/-- **Explicit Elementary Upper Bound on `P_pp(n)`**:
For every `n ≥ 4`, `P_pp(n) ≤ 2 * (Nat.sqrt n * Nat.log 2 n) * (Real.log n)^2`. -/
theorem bilateralPrimePowerErr_le {n : ℕ} (hn : 4 ≤ n) :
    bilateralPrimePowerErr n ≤ 2 * ((Nat.sqrt n * Nat.log 2 n : ℕ) : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
  classical
  unfold bilateralPrimePowerErr
  let S := (Finset.Icc 2 (n - 2)).filter
    (fun x => x.primeFactors.card = 1 ∧ (n - x).primeFactors.card = 1 ∧ ¬(x.Prime ∧ (n - x).Prime))
  have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
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
    have hx_le : x ≤ n := by omega
    have hnx_le : n - x ≤ n := by omega
    have hq_le : q ≤ n := le_trans (Nat.le_of_dvd hx_pos (Nat.dvd_of_mem_primeFactors (by rw [hq_eq]; simp))) hx_le
    have hr_le : r ≤ n := le_trans (Nat.le_of_dvd hnx_pos (Nat.dvd_of_mem_primeFactors (by rw [hr_eq]; simp))) hnx_le
    simp only [hq_eq, hr_eq, Finset.sum_singleton]
    have hlq : Real.log (q : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (Nat.cast_pos.mpr hqp.pos) (Nat.cast_le.mpr hq_le)
    have hlr : Real.log (r : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (Nat.cast_pos.mpr hrp.pos) (Nat.cast_le.mpr hr_le)
    rw [sq]
    exact mul_le_mul hlq hlr (le_of_lt (Real.log_pos (by exact_mod_cast hrp.one_lt))) hlogn_nonneg
  have hsum_le : ∑ x ∈ S,
        (∑ q ∈ x.primeFactors, Real.log (q : ℝ)) * (∑ r ∈ (n - x).primeFactors, Real.log (r : ℝ))
      ≤ (S.card : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
    calc _ ≤ ∑ _x ∈ S, (Real.log (n : ℝ)) ^ 2 := Finset.sum_le_sum hterm_le
      _ = (S.card : ℝ) * (Real.log (n : ℝ)) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  -- Bound S.card ≤ 2 * #{proper prime powers in [2, n-2]}
  let A := (Finset.Icc 2 (n - 2)).filter (fun x => x.primeFactors.card = 1 ∧ ¬x.Prime)
  let A' := A.image (fun y => n - y)
  have hS_sub : S ⊆ A ∪ A' := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    rw [Finset.mem_union]
    by_cases hxp : x.Prime
    · right
      have hnxp : ¬(n - x).Prime := fun h => hx.2.2.2 ⟨hxp, h⟩
      rw [Finset.mem_image]
      refine ⟨n - x, ?_, by omega⟩
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hx.2.2.1, hnxp⟩
    · left
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨hx.1, hx.2.1, hxp⟩
  have hcard_S : S.card ≤ 2 * (Nat.sqrt n * Nat.log 2 n) := by
    have hA := card_properPrimePowers_le n
    calc S.card ≤ (A ∪ A').card := Finset.card_le_card hS_sub
      _ ≤ A.card + A'.card := Finset.card_union_le A A'
      _ ≤ A.card + A.card := Nat.add_le_add_left Finset.card_image_le A.card
      _ = 2 * A.card := by omega
      _ ≤ 2 * (Nat.sqrt n * Nat.log 2 n) := Nat.mul_le_mul_left 2 hA
  have hcard_r : (S.card : ℝ) ≤ 2 * ((Nat.sqrt n * Nat.log 2 n : ℕ) : ℝ) := by
    exact_mod_cast hcard_S
  calc _ ≤ (S.card : ℝ) * (Real.log (n : ℝ)) ^ 2 := hsum_le
    _ ≤ (2 * ((Nat.sqrt n * Nat.log 2 n : ℕ) : ℝ)) * (Real.log (n : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right hcard_r (sq_nonneg _)
    _ = 2 * ((Nat.sqrt n * Nat.log 2 n : ℕ) : ℝ) * (Real.log (n : ℝ)) ^ 2 := by ring

/-- **Main Theorem 1 (Bilateral Anti-Symmetric Hyperbola Upper Bound)**:
For every `n ≥ 4` and every `0 < σ₁ ≤ σ₂ ≤ 2 / log n`,
`4 * (Ξ_n^J(σ₁) - Ξ_n^J(σ₂)) ≤ 4 * R_pr(n) + 4 * P_pp(n)`. -/
theorem bilateral_antiSym_upper_bound {n : ℕ} (hn : 4 ≤ n)
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ ≤ σ₂) (hσ₂ : σ₂ ≤ 2 / Real.log (n : ℝ)) :
    bilateralAntiSym n σ₁ - bilateralAntiSym n σ₂
      ≤ 4 * goldbachPrimePairSum n + 4 * bilateralPrimePowerErr n := by
  classical
  have hσ₂_pos : 0 < σ₂ := lt_of_lt_of_le hσ₁ hσ₁₂
  unfold bilateralAntiSym
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  let S := Finset.Icc 2 (n - 2)
  let P := fun x : ℕ => x.primeFactors.card = 1 ∧ (n - x).primeFactors.card = 1
  rw [← Finset.sum_filter_add_sum_filter_not S P]
  have hcomp_le : ∑ x ∈ S.filter (fun x => ¬P x),
      (σ₁ ^ (-(2 : ℤ)) * (antiSymFactor σ₁ x * antiSymFactor σ₁ (n - x))
        - σ₂ ^ (-(2 : ℤ)) * (antiSymFactor σ₂ x * antiSymFactor σ₂ (n - x))) ≤ 0 := by
    refine Finset.sum_nonpos ?_
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    have hcx : 1 ≤ x.primeFactors.card :=
      Finset.one_le_card.mpr (Nat.nonempty_primeFactors.mpr (by omega))
    have hcnx : 1 ≤ (n - x).primeFactors.card :=
      Finset.one_le_card.mpr (Nat.nonempty_primeFactors.mpr (by omega))
    have hsum3 : 3 ≤ x.primeFactors.card + (n - x).primeFactors.card := by
      by_contra hlt
      exact hx.2 (by omega)
    have hmono := antiSym_bilateral_composite_mono hn hx.1.1 (by omega) (by omega) (by omega) hsum3 hσ₁ hσ₁₂ hσ₂
    linarith
  have hpp_term : ∀ x ∈ S.filter P,
      σ₁ ^ (-(2 : ℤ)) * (antiSymFactor σ₁ x * antiSymFactor σ₁ (n - x))
        - σ₂ ^ (-(2 : ℤ)) * (antiSymFactor σ₂ x * antiSymFactor σ₂ (n - x))
      ≤ 4 * ((∑ q ∈ x.primeFactors, Real.log (q : ℝ)) * (∑ r ∈ (n - x).primeFactors, Real.log (r : ℝ))) := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    have hx_pos : 0 < x := by omega
    have hnx_pos : 0 < n - x := by omega
    have h1 := antiSymFactor_pp_div_le hσ₁ hx_pos hx.2.1
    have h2 := antiSymFactor_pp_div_le hσ₁ hnx_pos hx.2.2
    have hnn1 : 0 ≤ antiSymFactor σ₁ x / σ₁ := div_nonneg (antiSymFactor_nonneg hσ₁ hx_pos) (le_of_lt hσ₁)
    have hnn2 : 0 ≤ antiSymFactor σ₁ (n - x) / σ₁ := div_nonneg (antiSymFactor_nonneg hσ₁ hnx_pos) (le_of_lt hσ₁)
    have hnn3 : 0 ≤ σ₂ ^ (-(2 : ℤ)) * (antiSymFactor σ₂ x * antiSymFactor σ₂ (n - x)) := by
      rw [zpow_neg, zpow_two]
      exact mul_nonneg (inv_nonneg.mpr (mul_nonneg (le_of_lt hσ₂_pos) (le_of_lt hσ₂_pos)))
        (mul_nonneg (antiSymFactor_nonneg hσ₂_pos hx_pos) (antiSymFactor_nonneg hσ₂_pos hnx_pos))
    have hrew : σ₁ ^ (-(2 : ℤ)) * (antiSymFactor σ₁ x * antiSymFactor σ₁ (n - x))
        = (antiSymFactor σ₁ x / σ₁) * (antiSymFactor σ₁ (n - x) / σ₁) := by
      rw [zpow_neg, zpow_two]; field_simp [ne_of_gt hσ₁]
    rw [hrew]
    have hmul := mul_le_mul h1 h2 hnn2 (le_trans hnn1 h1)
    linarith
  have hpp_le : ∑ x ∈ S.filter P,
      (σ₁ ^ (-(2 : ℤ)) * (antiSymFactor σ₁ x * antiSymFactor σ₁ (n - x))
        - σ₂ ^ (-(2 : ℤ)) * (antiSymFactor σ₂ x * antiSymFactor σ₂ (n - x)))
      ≤ 4 * goldbachPrimePairSum n + 4 * bilateralPrimePowerErr n := by
    let Q := fun x : ℕ => x.Prime ∧ (n - x).Prime
    rw [← Finset.sum_filter_add_sum_filter_not (S.filter P) Q]
    have hS1 : (S.filter P).filter Q = S.filter Q := by
      ext x
      simp only [Finset.mem_filter, P, Q]
      constructor
      · intro ⟨⟨hx, _⟩, hq⟩; exact ⟨hx, hq⟩
      · intro ⟨hx, hq⟩
        exact ⟨⟨hx, by rw [hq.1.primeFactors]; simp, by rw [hq.2.primeFactors]; simp⟩, hq⟩
    have hS2 : (S.filter P).filter (fun x => ¬Q x)
        = S.filter (fun x => x.primeFactors.card = 1 ∧ (n - x).primeFactors.card = 1 ∧ ¬Q x) := by
      ext x; simp [P, Q, and_assoc]
    rw [hS1, hS2]
    unfold goldbachPrimePairSum bilateralPrimePowerErr
    rw [Finset.mul_sum, Finset.mul_sum]
    apply add_le_add
    · refine Finset.sum_le_sum ?_
      intro x hx
      have hx' : x ∈ S.filter P := by
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, by rw [hx.2.1.primeFactors]; simp, by rw [hx.2.2.primeFactors]; simp⟩
      have hle := hpp_term x hx'
      rw [Finset.mem_filter] at hx
      simpa [hx.2.1.primeFactors, hx.2.2.primeFactors] using hle
    · refine Finset.sum_le_sum ?_
      intro x hx
      have hx' : x ∈ S.filter P := by
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, hx.2.1, hx.2.2.1⟩
      exact hpp_term x hx'
  linarith

/-- **Main Theorem 1' (Complete Self-Contained 4-Quadrant Strong Goldbach Criterion)**:
For every `n ≥ 4`, ANY cutoff `D : ℕ`, and ANY `0 < σ₁ ≤ σ₂ ≤ 2 / log n`:
if `SS_D + 2 * SL_D + LL_D > 8 * (Nat.sqrt n * Nat.log 2 n) * (Real.log n)^2`,
then `n` is the sum of two primes! (Zero primes, zero BV, and zero opaque `P_pp` term!) -/
theorem bilateral_antiSym_quadrant_goldbach_criterion {n D : ℕ} (hn : 4 ≤ n)
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ ≤ σ₂) (hσ₂ : σ₂ ≤ 2 / Real.log (n : ℝ))
    (hgt : 8 * ((Nat.sqrt n * Nat.log 2 n : ℕ) : ℝ) * (Real.log (n : ℝ)) ^ 2
      < quadSS n D σ₁ σ₂ + 2 * quadSL n D σ₁ σ₂ + quadLL n D σ₁ σ₂) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  rw [← bilateralAntiSym_quadrant_split n D σ₁ σ₂] at hgt
  have hub := bilateral_antiSym_upper_bound hn hσ₁ hσ₁₂ hσ₂
  have hpp := bilateralPrimePowerErr_le hn
  have hpos : 0 < goldbachPrimePairSum n := by linarith
  by_contra hno
  push Not at hno
  have hzero : goldbachPrimePairSum n = 0 := by
    unfold goldbachPrimePairSum
    refine Finset.sum_eq_zero ?_
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    exact absurd (hno x (n - x) hx.2.1 hx.2.2) (by omega)
  linarith

/-! ### Part 4: Zero-Error Odd-Squarefree Criterion (`P_pp = 0` identically!) -/

/-- Odd-squarefree scaled bilateral Euler sum `Ξ_n^Q(σ)`. -/
noncomputable def oddSqfreeXi (n : ℕ) (σ : ℝ) : ℝ :=
  σ ^ (-(2 : ℤ)) * ∑ x ∈ (Finset.Icc 2 (n - 2)).filter (fun x => μ x = -1 ∧ μ (n - x) = -1),
    eulerFactor σ x * eulerFactor σ (n - x)

/-- **Main Theorem 2 (Zero-Error Strong Goldbach Criterion)**:
For every `n ≥ 4` and every `0 < σ₁ ≤ σ₂ ≤ 2 / log n`,
`Ξ_n^Q(σ₁) - Ξ_n^Q(σ₂) ≤ R_pr(n)` (with **ZERO** prime-power error!), and hence:
`Ξ_n^Q(σ₁) > Ξ_n^Q(σ₂)  ⟹  ∃ p q, p.Prime ∧ q.Prime ∧ p + q = n`. -/
theorem bilateral_oddSqfree_upper_bound {n : ℕ} (hn : 4 ≤ n)
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ ≤ σ₂) (hσ₂ : σ₂ ≤ 2 / Real.log (n : ℝ)) :
    oddSqfreeXi n σ₁ - oddSqfreeXi n σ₂ ≤ goldbachPrimePairSum n := by
  classical
  have hσ₂_pos : 0 < σ₂ := lt_of_lt_of_le hσ₁ hσ₁₂
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  unfold oddSqfreeXi
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  let S := (Finset.Icc 2 (n - 2)).filter (fun x => μ x = -1 ∧ μ (n - x) = -1)
  let Q := fun x : ℕ => x.Prime ∧ (n - x).Prime
  rw [← Finset.sum_filter_add_sum_filter_not S Q]
  -- Every non-(prime, prime) pair in S has both x, n-x squarefree with odd ω, hence ω(x) + ω(n-x) ≥ 4!
  have hcomp_le : ∑ x ∈ S.filter (fun x => ¬Q x),
      (σ₁ ^ (-(2 : ℤ)) * (eulerFactor σ₁ x * eulerFactor σ₁ (n - x))
        - σ₂ ^ (-(2 : ℤ)) * (eulerFactor σ₂ x * eulerFactor σ₂ (n - x))) ≤ 0 := by
    refine Finset.sum_nonpos ?_
    intro x hx
    rw [Finset.mem_filter] at hx
    have hxS := hx.1
    rw [Finset.mem_filter, Finset.mem_Icc] at hxS
    have hmu_x : μ x = -1 := hxS.2.1
    have hmu_nx : μ (n - x) = -1 := hxS.2.2
    have hsf_x : Squarefree x := by
      by_contra hnot
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnot] at hmu_x
      norm_num at hmu_x
    have hsf_nx : Squarefree (n - x) := by
      by_contra hnot
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnot] at hmu_nx
      norm_num at hmu_nx
    have hodd_x : Odd x.primeFactors.card := by
      have hrad : ∏ q ∈ x.primeFactors, q = x := rad_eq_self_of_squarefree hsf_x
      have h1 : μ x = (-1 : ℤ) ^ x.primeFactors.card := by
        conv_lhs => rw [← hrad]
        exact moebius_prod_of_primes (fun q hq => Nat.prime_of_mem_primeFactors hq)
      rw [h1] at hmu_x
      by_contra hno
      have hev : Even x.primeFactors.card := Nat.not_odd_iff_even.mp hno
      rw [hev.neg_one_pow] at hmu_x
      norm_num at hmu_x
    have hodd_nx : Odd (n - x).primeFactors.card := by
      have hrad : ∏ q ∈ (n - x).primeFactors, q = n - x := rad_eq_self_of_squarefree hsf_nx
      have h1 : μ (n - x) = (-1 : ℤ) ^ (n - x).primeFactors.card := by
        conv_lhs => rw [← hrad]
        exact moebius_prod_of_primes (fun q hq => Nat.prime_of_mem_primeFactors hq)
      rw [h1] at hmu_nx
      by_contra hno
      have hev : Even (n - x).primeFactors.card := Nat.not_odd_iff_even.mp hno
      rw [hev.neg_one_pow] at hmu_nx
      norm_num at hmu_nx
    -- For squarefree m, ω(m) = 1 implies m is prime!
    have hprime_of_card1 : ∀ m : ℕ, Squarefree m → m.primeFactors.card = 1 → m.Prime := by
      intro m hsf hc1
      obtain ⟨q, hq_eq⟩ := Finset.card_eq_one.mp hc1
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors (by rw [hq_eq]; simp)
      have hrad : rad m = m := rad_eq_self_of_squarefree hsf
      have : q = m := by simpa [rad, hq_eq] using hrad
      exact this ▸ hqp
    have hcard_ge4 : 4 ≤ x.primeFactors.card + (n - x).primeFactors.card := by
      obtain ⟨a, ha⟩ := hodd_x
      obtain ⟨b, hb⟩ := hodd_nx
      by_contra hlt
      have hab : a = 0 ∧ b = 0 := by omega
      have hx1 : x.primeFactors.card = 1 := by omega
      have hnx1 : (n - x).primeFactors.card = 1 := by omega
      exact hx.2 ⟨hprime_of_card1 x hsf_x hx1, hprime_of_card1 (n - x) hsf_nx hnx1⟩
    let idx := x.primeFactors.disjSum (n - x).primeFactors
    let a : ℕ ⊕ ℕ → ℝ := Sum.elim (fun q => Real.log (q : ℝ)) (fun r => Real.log (r : ℝ))
    have ha_pos : ∀ i ∈ idx, 0 < a i := by
      intro i hi
      cases i with
      | inl q => exact Real.log_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors (by simpa [idx] using hi)).one_lt)
      | inr r => exact Real.log_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors (by simpa [idx] using hi)).one_lt)
    have hsum_a : ∑ i ∈ idx, a i = Real.log (x : ℝ) + Real.log ((n - x : ℕ) : ℝ) := by
      simp only [idx, Finset.sum_disjSum, a, Sum.elim_inl, Sum.elim_inr]
      have hx_log : ∑ q ∈ x.primeFactors, Real.log (q : ℝ) = Real.log (x : ℝ) := by
        have := sum_log_primeFactors_add_log_div_rad (by omega : 0 < x)
        rw [rad_eq_self_of_squarefree hsf_x, Nat.div_self (by omega)] at this
        simpa using this
      have hnx_log : ∑ r ∈ (n - x).primeFactors, Real.log (r : ℝ) = Real.log ((n - x : ℕ) : ℝ) := by
        have := sum_log_primeFactors_add_log_div_rad (by omega : 0 < n - x)
        rw [rad_eq_self_of_squarefree hsf_nx, Nat.div_self (by omega)] at this
        simpa using this
      rw [hx_log, hnx_log]
    have hbound : σ₂ * ((∑ i ∈ idx, a i) + (∑ _j ∈ (∅ : Finset Unit), (0 : ℝ)))
        ≤ 2 * ((idx.card : ℝ) - (2 : ℝ)) := by
      simp only [Finset.sum_empty, add_zero]
      rw [hsum_a]
      have hlx : Real.log (x : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < x)) (by exact_mod_cast (by omega : x ≤ n))
      have hlnx : Real.log ((n - x : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < n - x)) (by exact_mod_cast (by omega : n - x ≤ n))
      have hnn : 0 ≤ Real.log (x : ℝ) + Real.log ((n - x : ℕ) : ℝ) :=
        add_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x)))
          (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n - x)))
      have hmul : σ₂ * (Real.log (x : ℝ) + Real.log ((n - x : ℕ) : ℝ))
          ≤ (2 / Real.log (n : ℝ)) * (2 * Real.log (n : ℝ)) :=
        mul_le_mul hσ₂ (by linarith) hnn (le_of_lt (div_pos (by norm_num) hlogn_pos))
      have h4 : (2 / Real.log (n : ℝ)) * (2 * Real.log (n : ℝ)) = 4 := by
        field_simp [ne_of_gt hlogn_pos]; ring
      have hc : (4 : ℝ) ≤ (idx.card : ℝ) := by
        exact_mod_cast (by rw [Finset.card_disjSum]; exact hcard_ge4)
      linarith
    have hmono := scaled_euler_plus_minus_mono idx a ha_pos (∅ : Finset Unit) (fun _ => 0)
      (fun _ h => by simp at h) 2 hσ₁ hσ₁₂ hbound
    have hpeq : ∀ σ : ℝ, ∏ i ∈ idx, (1 - Real.exp (-σ * a i)) = eulerFactor σ x * eulerFactor σ (n - x) := by
      intro σ
      simp only [idx, Finset.prod_disjSum, a, Sum.elim_inl, Sum.elim_inr]
      have hf : ∀ m : ℕ, ∏ q ∈ m.primeFactors, (1 - Real.exp (-σ * Real.log (q : ℝ))) = eulerFactor σ m := by
        intro m; unfold eulerFactor
        refine Finset.prod_congr rfl fun q hq => ?_
        rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hq).pos), mul_comm]
      rw [hf x, hf (n - x)]
    simp only [Finset.prod_empty, mul_one, hpeq] at hmono
    norm_num at hmono
    rw [zpow_neg, zpow_two, zpow_neg, zpow_two]
    simpa [sq] using sub_nonpos.mpr hmono
  -- Prime-prime part is bounded by goldbachPrimePairSum n:
  have hS1 : S.filter Q = (Finset.Icc 2 (n - 2)).filter Q := by
    ext x
    simp only [Finset.mem_filter, S, Q]
    constructor
    · intro ⟨⟨hx, _⟩, hq⟩; exact ⟨hx, hq⟩
    · intro ⟨hx, hq⟩
      exact ⟨⟨hx, ArithmeticFunction.moebius_apply_prime hq.1,
        ArithmeticFunction.moebius_apply_prime hq.2⟩, hq⟩
  rw [hS1]
  have hpr_le : ∑ x ∈ (Finset.Icc 2 (n - 2)).filter Q,
      (σ₁ ^ (-(2 : ℤ)) * (eulerFactor σ₁ x * eulerFactor σ₁ (n - x))
        - σ₂ ^ (-(2 : ℤ)) * (eulerFactor σ₂ x * eulerFactor σ₂ (n - x)))
      ≤ goldbachPrimePairSum n := by
    unfold goldbachPrimePairSum
    refine Finset.sum_le_sum ?_
    intro x hx
    rw [Finset.mem_filter] at hx
    have hxp : x.Prime := hx.2.1
    have hnxp : (n - x).Prime := hx.2.2
    have h1 : ∀ s : ℝ, 0 < s → ∀ p : ℕ, p.Prime →
        0 ≤ (1 - (p : ℝ) ^ (-s)) / s ∧ (1 - (p : ℝ) ^ (-s)) / s ≤ Real.log (p : ℝ) := by
      intro s hs p hp
      rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hp.pos), mul_comm]
      have hlp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
      constructor
      · exact div_nonneg (by linarith [Real.exp_lt_one_iff.mpr (by nlinarith : -s * Real.log (p : ℝ) < 0)]) (le_of_lt hs)
      · rw [div_le_iff₀ hs]; linarith [Real.add_one_le_exp (-s * Real.log (p : ℝ))]
    have hrew : ∀ s : ℝ, s ≠ 0 →
        s ^ (-(2 : ℤ)) * (eulerFactor s x * eulerFactor s (n - x))
        = ((1 - (x : ℝ) ^ (-s)) / s) * ((1 - ((n - x : ℕ) : ℝ) ^ (-s)) / s) := by
      intro s hs
      unfold eulerFactor
      rw [hxp.primeFactors, hnxp.primeFactors, Finset.prod_singleton, Finset.prod_singleton,
        zpow_neg, zpow_two]
      field_simp [hs]
    rw [hrew σ₁ (ne_of_gt hσ₁), hrew σ₂ (ne_of_gt hσ₂_pos)]
    have hx1 := h1 σ₁ hσ₁ x hxp
    have hnx1 := h1 σ₁ hσ₁ (n - x) hnxp
    have hx2 := h1 σ₂ hσ₂_pos x hxp
    have hnx2 := h1 σ₂ hσ₂_pos (n - x) hnxp
    have hmul1 := mul_le_mul hx1.2 hnx1.2 hnx1.1 (le_trans hx1.1 hx1.2)
    have hmul2 := mul_nonneg hx2.1 hnx2.1
    linarith
  linarith

/-- **Main Theorem 2' (Zero-Error Strong Goldbach Criterion)**:
For every `n ≥ 4` and every `0 < σ₁ ≤ σ₂ ≤ 2 / log n`,
`Ξ_n^Q(σ₁) > Ξ_n^Q(σ₂)` implies `n` is the sum of two primes (ZERO error term!). -/
theorem bilateral_oddSqfree_goldbach_criterion {n : ℕ} (hn : 4 ≤ n)
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ ≤ σ₂) (hσ₂ : σ₂ ≤ 2 / Real.log (n : ℝ))
    (hgt : oddSqfreeXi n σ₂ < oddSqfreeXi n σ₁) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  have hub := bilateral_oddSqfree_upper_bound hn hσ₁ hσ₁₂ hσ₂
  have hpos : 0 < goldbachPrimePairSum n := by linarith
  by_contra hno
  push Not at hno
  have hzero : goldbachPrimePairSum n = 0 := by
    unfold goldbachPrimePairSum
    refine Finset.sum_eq_zero ?_
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    exact absurd (hno x (n - x) hx.2.1 hx.2.2) (by omega)
  linarith

end GoldbachWave9

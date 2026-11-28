import Mathlib

/-!
# Mellin–Euler Sign-Separation Criteria for Strong Goldbach

This file proves two unconditional, kernel-checked one-sided criteria for the
Strong (binary) Goldbach conjecture, together with their exact Möbius–divisor
and prime-free CRT hyperbola identities.

1. **Elementary analytic core (`h_ge_one_sub_half`, `scaled_euler_prod_mono`)**:
   For every `u > 0`, `u / (exp u - 1) ≥ 1 - u / 2`. Consequently, for any finite
   indexed family of positive reals `(a_i)_{i ∈ s}` with `s.card ≥ r + 1` and any
   `0 < σ₁ ≤ σ₂` satisfying `σ₂ * ∑ i ∈ s, a i ≤ 2 * (s.card - r)`,
   `σ₁^(-r) * ∏ i ∈ s, (1 - exp (-σ₁ * a i)) ≤ σ₂^(-r) * ∏ i ∈ s, (1 - exp (-σ₂ * a i))`.

2. **Bilateral Prime-Free CRT Criterion (`bilateral_mellin_euler_goldbach_criterion`)**:
   Define the completely prime-free CRT–Möbius function
   `B_n°(σ) := ∑ x ∈ [2, n - 2], eulerFactor σ x * eulerFactor σ (n - x)`
   and prove `B_n°(σ) = ∑ d₁ ∈ [1, n-2], ∑ d₂ ∈ [1, n-2], μ(d₁) μ(d₂) (d₁ d₂)^(-σ) * N_n°(d₁, d₂)`
   where `N_n°(d₁, d₂) = #{x ∈ [2, n - 2] : d₁ ∣ x ∧ d₂ ∣ (n - x)}`.
   Setting `Ξ_n°(σ) := σ^(-2) * B_n°(σ)`, for every `n ≥ 4` and `0 < σ₁ ≤ σ₂ ≤ 1 / log n`:
   `Ξ_n°(σ₁) - Ξ_n°(σ₂) ≤ R_pr(n) + P_pp_bilat(n)`,
   and `Ξ_n°(σ₁) - Ξ_n°(σ₂) > P_pp_bilat(n)` implies Strong Goldbach at `n`.

3. **One-Sided Mellin–Euler Criterion (`oneSided_mellin_euler_goldbach_criterion`)**:
   Define `G_n°(σ) := ∑ p ∈ [2, n - 2], (if p.Prime then log p else 0) * eulerFactor σ (n - p)`
   and prove `G_n°(σ) = ∑ d ∈ [1, n - 2], μ(d) d^(-σ) * θ_n°(d)`.
   Setting `Φ_n°(σ) := σ^(-1) * G_n°(σ)`, for every `n ≥ 4` and `0 < σ₁ ≤ σ₂ ≤ 2 / log n`:
   `Φ_n°(σ₁) - Φ_n°(σ₂) ≤ R_pr(n) + P_pp_one(n)`,
   and `Φ_n°(σ₁) - Φ_n°(σ₂) > P_pp_one(n)` implies Strong Goldbach at `n`.

Honesty note: these theorems are unconditional reductions/criteria and do NOT
claim a proof of Strong Goldbach; establishing `Ξ_n°(σ₁) - Ξ_n°(σ₂) > P_pp_bilat(n)`
for all large even `n` remains open and reduces directly to cancellation in the
long-range binary Möbius correlation (`d₁ d₂ > Y`).
-/

open scoped BigOperators ArithmeticFunction.Moebius
open Finset Real ArithmeticFunction

namespace GoldbachAttack

/-! ### Part 1: Elementary analytic core -/

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
    have hmul1 : HasDerivAt (fun x : ℝ => (2 + x) * Real.exp (-x / 2))
        (1 * Real.exp (-t / 2) + (2 + t) * (Real.exp (-t / 2) * (-1 / 2))) t := h1.mul h2
    have hmul2 : HasDerivAt (fun x : ℝ => (2 - x) * Real.exp (x / 2))
        ((-1) * Real.exp (t / 2) + (2 - t) * (Real.exp (t / 2) * (1 / 2))) t := h3.mul h4
    exact (hmul1.sub hmul2).congr_deriv (by ring)
  have hf_mono : MonotoneOn f (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hf_deriv t).continuousAt.continuousWithinAt
    · exact fun t _ => (hf_deriv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hf_deriv t).deriv]
      have ht0 : 0 ≤ t := le_of_lt (by simpa [interior_Ici] using ht)
      have hexp : Real.exp (-t / 2) ≤ Real.exp (t / 2) :=
        Real.exp_le_exp.mpr (by linarith)
      exact mul_nonneg (by linarith) (sub_nonneg.mpr hexp)
  have h0 : f 0 = 0 := by simp [f]
  have := hf_mono (Set.mem_Ici.mpr le_rfl) hu hu
  simpa [h0, f] using this

/-- Core inequality: for every `u > 0`, `u / (exp u - 1) ≥ 1 - u / 2`. -/
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

/-- Scaled Euler product monotonicity for any finite indexed family of positive reals.
If `σ₂ * ∑ i ∈ s, a i ≤ 2 * (s.card - r)` and `0 < σ₁ ≤ σ₂`, then
`σ₁^(-r) * ∏ i ∈ s, (1 - exp (-σ₁ * a i)) ≤ σ₂^(-r) * ∏ i ∈ s, (1 - exp (-σ₂ * a i))`. -/
lemma scaled_euler_prod_mono {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (r : ℕ)
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ ≤ σ₂)
    (hbound : σ₂ * ∑ i ∈ s, a i ≤ 2 * ((s.card : ℝ) - (r : ℝ))) :
    σ₁ ^ (-(r : ℤ)) * ∏ i ∈ s, (1 - Real.exp (-σ₁ * a i)) ≤
      σ₂ ^ (-(r : ℤ)) * ∏ i ∈ s, (1 - Real.exp (-σ₂ * a i)) := by
  let g : ℝ → ℝ := fun σ =>
    (∑ i ∈ s, Real.log (1 - Real.exp (-σ * a i))) - (r : ℝ) * Real.log σ
  have hpos_term : ∀ σ ∈ Set.Icc σ₁ σ₂, ∀ i ∈ s, 0 < 1 - Real.exp (-σ * a i) := by
    intro σ hσ i hi
    have hσ_pos : 0 < σ := lt_of_lt_of_le hσ₁ hσ.1
    have : -σ * a i < 0 := by nlinarith [ha i hi]
    linarith [Real.exp_lt_one_iff.mpr this]
  have hg_deriv : ∀ σ ∈ Set.Icc σ₁ σ₂,
      HasDerivAt g
        ((∑ i ∈ s, a i * Real.exp (-σ * a i) / (1 - Real.exp (-σ * a i))) - (r : ℝ) / σ) σ := by
    intro σ hσ
    have hσ_pos : 0 < σ := lt_of_lt_of_le hσ₁ hσ.1
    have hsum : HasDerivAt (fun t => ∑ i ∈ s, Real.log (1 - Real.exp (-t * a i)))
        (∑ i ∈ s, a i * Real.exp (-σ * a i) / (1 - Real.exp (-σ * a i))) σ := by
      apply HasDerivAt.fun_sum
      intro i hi
      have hlin : HasDerivAt (fun t : ℝ => -t * a i) (-a i) σ := by
        simpa using (hasDerivAt_id σ).neg.mul_const (a i)
      have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t * a i))
          (Real.exp (-σ * a i) * (-a i)) σ := hlin.exp
      have hsub : HasDerivAt (fun t : ℝ => 1 - Real.exp (-t * a i))
          (a i * Real.exp (-σ * a i)) σ :=
        (hexp.const_sub (1 : ℝ)).congr_deriv (by ring)
      exact hsub.log (ne_of_gt (hpos_term σ hσ i hi))
    have hlog : HasDerivAt (fun t : ℝ => (r : ℝ) * Real.log t) ((r : ℝ) / σ) σ :=
      ((Real.hasDerivAt_log (ne_of_gt hσ_pos)).const_mul (r : ℝ)).congr_deriv (by ring)
    exact hsum.sub hlog
  have hg_mono : MonotoneOn g (Set.Icc σ₁ σ₂) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc σ₁ σ₂)
    · exact fun σ hσ => (hg_deriv σ hσ).continuousAt.continuousWithinAt
    · exact fun σ hσ => (hg_deriv σ (interior_subset hσ)).differentiableAt.differentiableWithinAt
    · intro σ hσ
      have hσ_mem : σ ∈ Set.Icc σ₁ σ₂ := interior_subset hσ
      have hσ_pos : 0 < σ := lt_of_lt_of_le hσ₁ hσ_mem.1
      rw [(hg_deriv σ hσ_mem).deriv]
      have hterm_ge : ∀ i ∈ s,
          (1 - σ * a i / 2) / σ ≤ a i * Real.exp (-σ * a i) / (1 - Real.exp (-σ * a i)) := by
        intro i hi
        have hai : 0 < a i := ha i hi
        have hu : 0 < σ * a i := mul_pos hσ_pos hai
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
      have hsum_ge := Finset.sum_le_sum hterm_ge
      have hsum_eval : ∑ i ∈ s, (1 - σ * a i / 2) / σ
          = ((s.card : ℝ) - σ * (∑ i ∈ s, a i) / 2) / σ := by
        rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
        have : ∑ i ∈ s, σ * a i / 2 = σ * (∑ i ∈ s, a i) / 2 := by
          rw [← Finset.sum_div, ← Finset.mul_sum]
        rw [this]
      rw [hsum_eval] at hsum_ge
      have hsum_a_nonneg : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg (fun i hi => le_of_lt (ha i hi))
      have hσ_le : σ * ∑ i ∈ s, a i ≤ σ₂ * ∑ i ∈ s, a i :=
        mul_le_mul_of_nonneg_right hσ_mem.2 hsum_a_nonneg
      have hnum : 0 ≤ ((s.card : ℝ) - σ * (∑ i ∈ s, a i) / 2) - (r : ℝ) := by linarith
      have hdiv : 0 ≤ (((s.card : ℝ) - σ * (∑ i ∈ s, a i) / 2) - (r : ℝ)) / σ :=
        div_nonneg hnum (le_of_lt hσ_pos)
      have hsub_div : ((s.card : ℝ) - σ * (∑ i ∈ s, a i) / 2) / σ - (r : ℝ) / σ
          = (((s.card : ℝ) - σ * (∑ i ∈ s, a i) / 2) - (r : ℝ)) / σ := by ring
      linarith
  have hg_le : g σ₁ ≤ g σ₂ := hg_mono ⟨le_rfl, hσ₁₂⟩ ⟨hσ₁₂, le_rfl⟩ hσ₁₂
  have hexp_le : Real.exp (g σ₁) ≤ Real.exp (g σ₂) := Real.exp_le_exp.mpr hg_le
  have hexp_eq : ∀ σ ∈ Set.Icc σ₁ σ₂,
      Real.exp (g σ) = σ ^ (-(r : ℤ)) * ∏ i ∈ s, (1 - Real.exp (-σ * a i)) := by
    intro σ hσ
    have hσ_pos : 0 < σ := lt_of_lt_of_le hσ₁ hσ.1
    simp only [g, Real.exp_sub, Real.exp_sum]
    have hprod : ∏ i ∈ s, Real.exp (Real.log (1 - Real.exp (-σ * a i)))
        = ∏ i ∈ s, (1 - Real.exp (-σ * a i)) :=
      Finset.prod_congr rfl (fun i hi => Real.exp_log (hpos_term σ hσ i hi))
    rw [hprod]
    have hpow : Real.exp ((r : ℝ) * Real.log σ) = σ ^ r := by
      rw [mul_comm, ← Real.rpow_def_of_pos hσ_pos, Real.rpow_natCast]
    rw [hpow, zpow_neg, zpow_natCast, div_eq_inv_mul]
  rw [hexp_eq σ₁ ⟨le_rfl, hσ₁₂⟩, hexp_eq σ₂ ⟨hσ₁₂, le_rfl⟩] at hexp_le
  exact hexp_le

/-! ### Part 2: Exact Euler-product / Möbius divisor identities -/

/-- The Euler product `∏_{q | m} (1 - q^(-σ))` for `m : ℕ`. -/
noncomputable def eulerFactor (σ : ℝ) (m : ℕ) : ℝ :=
  ∏ q ∈ m.primeFactors, (1 - (q : ℝ) ^ (-σ))

/-- For `q ≥ 1`, `(q : ℝ)^(-σ) = exp (-σ * log q)`. -/
lemma nat_rpow_neg_eq_exp (σ : ℝ) {q : ℕ} (hq : 0 < q) :
    (q : ℝ) ^ (-σ) = Real.exp (-σ * Real.log (q : ℝ)) := by
  have hq' : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  rw [Real.rpow_def_of_pos hq', mul_comm]

/-- `eulerFactor σ m` rewritten using `Real.exp`. -/
lemma eulerFactor_eq_exp_prod (σ : ℝ) (m : ℕ) :
    eulerFactor σ m = ∏ q ∈ m.primeFactors, (1 - Real.exp (-σ * Real.log (q : ℝ))) := by
  unfold eulerFactor
  refine Finset.prod_congr rfl ?_
  intro q hq
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  rw [nat_rpow_neg_eq_exp σ hqp.pos]

/-- Helper: product of a finset of distinct primes is squarefree. -/
lemma squarefree_prod_of_primes {t : Finset ℕ} (ht : ∀ q ∈ t, q.Prime) :
    Squarefree (∏ q ∈ t, q) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert p s hps ih =>
    rw [Finset.prod_insert hps]
    have hp : p.Prime := ht p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => ht q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hq' : q.Prime := hs q hq
      have hne : p ≠ q := fun h => hps (h ▸ hq)
      exact (Nat.coprime_primes hp hq').mpr hne
    exact (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, ih hs⟩

/-- Helper: Möbius function of a product of distinct primes is `(-1)^t.card`. -/
lemma moebius_prod_of_primes {t : Finset ℕ} (ht : ∀ q ∈ t, q.Prime) :
    μ (∏ q ∈ t, q) = (-1 : ℤ) ^ t.card := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert p s hps ih =>
    rw [Finset.prod_insert hps, Finset.card_insert_of_notMem hps, pow_succ']
    have hp : p.Prime := ht p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => ht q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      exact (Nat.coprime_primes hp (hs q hq)).mpr (fun h => hps (h ▸ hq))
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime hp, ih hs]

/-- Helper: rpow distributes over a finite product of positive naturals. -/
lemma prod_nat_rpow (σ : ℝ) (t : Finset ℕ) :
    ((∏ q ∈ t, q : ℕ) : ℝ) ^ σ = ∏ q ∈ t, (q : ℝ) ^ σ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert p s hps ih =>
    rw [Finset.prod_insert hps, Finset.prod_insert hps, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg _), ih]

/-- Helper: a squarefree positive natural equals the product of its prime factors. -/
lemma prod_primeFactors_eq_self_of_squarefree {d : ℕ} (hd : Squarefree d) :
    ∏ q ∈ d.primeFactors, q = d := by
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
      have : p ^ 2 ∣ d := (hpp.pow_dvd_iff_le_factorization hne).mpr hgt
      simpa [sq] using this
    exact hpp.ne_one (Nat.isUnit_iff.mp (hd p hp2))
  have heq1 : d.factorization p = 1 := le_antisymm hfac_le hfac_ge
  rw [heq1, pow_one]

/-- Exact Möbius–Euler identity: for `m ≥ 1`, `∏_{q | m} (1 - q^(-σ)) = ∑_{d | m} μ(d) d^(-σ)`. -/
lemma eulerFactor_eq_moebius_sum (σ : ℝ) {m : ℕ} (hm : 0 < m) :
    eulerFactor σ m = ∑ d ∈ m.divisors, (μ d : ℝ) * (d : ℝ) ^ (-σ) := by
  classical
  unfold eulerFactor
  have h1 : ∏ q ∈ m.primeFactors, (1 - (q : ℝ) ^ (-σ))
      = ∏ q ∈ m.primeFactors, (1 + (-(q : ℝ) ^ (-σ))) :=
    Finset.prod_congr rfl (fun _ _ => by ring)
  rw [h1, Finset.prod_one_add]
  have hfilter : ∑ d ∈ m.divisors, (μ d : ℝ) * (d : ℝ) ^ (-σ)
      = ∑ d ∈ m.divisors.filter Squarefree, (μ d : ℝ) * (d : ℝ) ^ (-σ) := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro d hd hnot
    rw [Finset.mem_filter] at hnot
    have hnsf : ¬ Squarefree d := fun hsf => hnot ⟨hd, hsf⟩
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsf]
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
    refine ⟨d.primeFactors, ?_, prod_primeFactors_eq_self_of_squarefree hd.2⟩
    rw [Finset.mem_powerset]
    exact Nat.primeFactors_mono hd.1.1 hd.1.2
  · intro t ht
    rw [Finset.mem_powerset] at ht
    have hpt : ∀ q ∈ t, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors (ht hq)
    rw [Finset.prod_neg, moebius_prod_of_primes hpt, prod_nat_rpow (-σ) t]
    push_cast
    rfl

/-! ### Part 3: Bilateral Prime-Free CRT Criterion for Strong Goldbach -/

/-- The bilateral Euler-product sum `B_n°(σ) = ∑_{x=2}^{n-2} eulerFactor σ x * eulerFactor σ (n-x)`. -/
noncomputable def bilateralEuler (n : ℕ) (σ : ℝ) : ℝ :=
  ∑ x ∈ Finset.Icc 2 (n - 2), eulerFactor σ x * eulerFactor σ (n - x)

/-- The scaled bilateral function `Ξ_n°(σ) = σ^(-2) * B_n°(σ)`. -/
noncomputable def bilateralXi (n : ℕ) (σ : ℝ) : ℝ :=
  σ ^ (-(2 : ℤ)) * bilateralEuler n σ

/-- Pure elementary CRT congruence count `N_n°(d₁, d₂) = #{x ∈ [2, n - 2] : d₁ ∣ x ∧ d₂ ∣ (n - x)}`. -/
def crtPairCount (n d₁ d₂ : ℕ) : ℕ :=
  ((Finset.Icc 2 (n - 2)).filter (fun x => d₁ ∣ x ∧ d₂ ∣ (n - x))).card

/-- Exact prime-free CRT expansion of `B_n°(σ)`. Zero primes appear on the RHS. -/
theorem bilateralEuler_eq_crt_sum (n : ℕ) (σ : ℝ) :
    bilateralEuler n σ =
      ∑ d₁ ∈ Finset.Icc 1 (n - 2), ∑ d₂ ∈ Finset.Icc 1 (n - 2),
        (μ d₁ : ℝ) * (μ d₂ : ℝ) * ((d₁ * d₂ : ℕ) : ℝ) ^ (-σ) * (crtPairCount n d₁ d₂ : ℝ) := by
  classical
  unfold bilateralEuler
  have h1 : ∑ x ∈ Finset.Icc 2 (n - 2), eulerFactor σ x * eulerFactor σ (n - x)
      = ∑ x ∈ Finset.Icc 2 (n - 2),
          ∑ d₁ ∈ Finset.Icc 1 (n - 2), ∑ d₂ ∈ Finset.Icc 1 (n - 2),
            if d₁ ∣ x ∧ d₂ ∣ (n - x) then
              (μ d₁ : ℝ) * (μ d₂ : ℝ) * ((d₁ * d₂ : ℕ) : ℝ) ^ (-σ)
            else 0 := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    rw [Finset.mem_Icc] at hx
    have hx_pos : 0 < x := by omega
    have hnx_pos : 0 < n - x := by omega
    have hnx_le : n - x ≤ n - 2 := by omega
    rw [eulerFactor_eq_moebius_sum σ hx_pos, eulerFactor_eq_moebius_sum σ hnx_pos,
      Finset.sum_mul_sum]
    have hsub₁ : x.divisors = (Finset.Icc 1 (n - 2)).filter (· ∣ x) := by
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · intro ⟨hd, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hd hx_pos, le_trans (Nat.le_of_dvd hx_pos hd) hx.2⟩, hd⟩
      · intro ⟨_, hd⟩
        exact ⟨hd, ne_of_gt hx_pos⟩
    have hsub₂ : (n - x).divisors = (Finset.Icc 1 (n - 2)).filter (· ∣ (n - x)) := by
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · intro ⟨hd, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hd hnx_pos, le_trans (Nat.le_of_dvd hnx_pos hd) hnx_le⟩, hd⟩
      · intro ⟨_, hd⟩
        exact ⟨hd, ne_of_gt hnx_pos⟩
    rw [hsub₁, hsub₂, Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro d₁ _
    by_cases hd₁ : d₁ ∣ x
    · simp only [hd₁, true_and, if_true, Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro d₂ _
      by_cases hd₂ : d₂ ∣ (n - x)
      · simp only [hd₂, if_true, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg d₁) (Nat.cast_nonneg d₂)]
        ring
      · simp [hd₂]
    · simp [hd₁]
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro d₁ _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro d₂ _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rfl

/-- Hyperbola split of `B_n°(σ)` into short CRT region `d₁ d₂ ≤ Y` and long Möbius correlation `d₁ d₂ > Y`. -/
theorem bilateralEuler_hyperbola_split (n Y : ℕ) (σ : ℝ) :
    bilateralEuler n σ =
      (∑ p ∈ ((Finset.Icc 1 (n - 2)) ×ˢ (Finset.Icc 1 (n - 2))).filter (fun p => p.1 * p.2 ≤ Y),
        (μ p.1 : ℝ) * (μ p.2 : ℝ) * ((p.1 * p.2 : ℕ) : ℝ) ^ (-σ) * (crtPairCount n p.1 p.2 : ℝ))
      +
      (∑ p ∈ ((Finset.Icc 1 (n - 2)) ×ˢ (Finset.Icc 1 (n - 2))).filter (fun p => Y < p.1 * p.2),
        (μ p.1 : ℝ) * (μ p.2 : ℝ) * ((p.1 * p.2 : ℕ) : ℝ) ^ (-σ) * (crtPairCount n p.1 p.2 : ℝ)) := by
  rw [bilateralEuler_eq_crt_sum, ← Finset.sum_product']
  have hpart := Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 (n - 2)) ×ˢ (Finset.Icc 1 (n - 2)))
    (fun p : ℕ × ℕ => p.1 * p.2 ≤ Y)
    (fun p => (μ p.1 : ℝ) * (μ p.2 : ℝ) * ((p.1 * p.2 : ℕ) : ℝ) ^ (-σ) * (crtPairCount n p.1 p.2 : ℝ))
  simpa [not_le] using hpart.symm

/-- Goldbach prime-pair sum `R_pr(n) = ∑_{x ∈ [2, n-2], x prime, n-x prime} log x * log (n - x)`. -/
noncomputable def goldbachPrimePairSum (n : ℕ) : ℝ :=
  ∑ x ∈ (Finset.Icc 2 (n - 2)).filter (fun x => x.Prime ∧ (n - x).Prime),
    Real.log (x : ℝ) * Real.log ((n - x : ℕ) : ℝ)

/-- Bilateral proper prime-power error sum: pairs `(x, n-x)` where both are prime powers
(`ω(x) = ω(n - x) = 1`), at least one is NOT prime, weighted by `Λ(x) Λ(n - x)`. -/
noncomputable def bilateralPrimePowerErr (n : ℕ) : ℝ :=
  ∑ x ∈ (Finset.Icc 2 (n - 2)).filter
      (fun x => x.primeFactors.card = 1 ∧ (n - x).primeFactors.card = 1 ∧ ¬(x.Prime ∧ (n - x).Prime)),
    (∑ q ∈ x.primeFactors, Real.log (q : ℝ)) * (∑ r ∈ (n - x).primeFactors, Real.log (r : ℝ))

/-- Elementary bound: `∑_{q | m} log q ≤ log m` for every `m ≥ 1`. -/
lemma sum_log_primeFactors_le_log {m : ℕ} (hm : 0 < m) :
    ∑ q ∈ m.primeFactors, Real.log (q : ℝ) ≤ Real.log (m : ℝ) := by
  have hprod_pos : 0 < ∏ q ∈ m.primeFactors, q :=
    Finset.prod_pos (fun q hq => (Nat.prime_of_mem_primeFactors hq).pos)
  have hprod_le : (∏ q ∈ m.primeFactors, q : ℕ) ≤ m :=
    Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)
  have hlog_prod : Real.log ((∏ q ∈ m.primeFactors, q : ℕ) : ℝ)
      = ∑ q ∈ m.primeFactors, Real.log (q : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    intro q hq
    exact ne_of_gt (Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hq).pos)
  rw [← hlog_prod]
  exact Real.log_le_log (Nat.cast_pos.mpr hprod_pos) (Nat.cast_le.mpr hprod_le)

/-- Elementary bound: for `σ > 0` and prime `q`, `0 ≤ (1 - q^(-σ)) / σ ≤ log q`. -/
lemma eulerFactor_prime_div_le_log {σ : ℝ} (hσ : 0 < σ) {q : ℕ} (hq : q.Prime) :
    0 ≤ (1 - (q : ℝ) ^ (-σ)) / σ ∧ (1 - (q : ℝ) ^ (-σ)) / σ ≤ Real.log (q : ℝ) := by
  rw [nat_rpow_neg_eq_exp σ hq.pos]
  have hlog_pos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hexp_lt : Real.exp (-σ * Real.log (q : ℝ)) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith)
  constructor
  · exact div_nonneg (by linarith) (le_of_lt hσ)
  · rw [div_le_iff₀ hσ]
    have hlin := Real.add_one_le_exp (-σ * Real.log (q : ℝ))
    linarith

/-- For any `x ∈ [2, n-2]` with `x.primeFactors.card = 1` and `(n-x).primeFactors.card = 1`:
`Ξ-term(σ₁) - Ξ-term(σ₂) ≤ (∑_{q|x} log q) * (∑_{r|n-x} log r)`. -/
lemma bilateral_pp_term_le {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
    {x y : ℕ} (hx1 : x.primeFactors.card = 1) (hy1 : y.primeFactors.card = 1) :
    σ₁ ^ (-(2 : ℤ)) * (eulerFactor σ₁ x * eulerFactor σ₁ y)
      - σ₂ ^ (-(2 : ℤ)) * (eulerFactor σ₂ x * eulerFactor σ₂ y)
    ≤ (∑ q ∈ x.primeFactors, Real.log (q : ℝ)) * (∑ r ∈ y.primeFactors, Real.log (r : ℝ)) := by
  obtain ⟨q, hq_eq⟩ := Finset.card_eq_one.mp hx1
  obtain ⟨r, hr_eq⟩ := Finset.card_eq_one.mp hy1
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors (by rw [hq_eq]; simp)
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors (by rw [hr_eq]; simp)
  simp only [eulerFactor, hq_eq, hr_eq, Finset.prod_singleton, Finset.sum_singleton]
  have hq1 := eulerFactor_prime_div_le_log hσ₁ hqp
  have hr1 := eulerFactor_prime_div_le_log hσ₁ hrp
  have hq2 := eulerFactor_prime_div_le_log hσ₂ hqp
  have hr2 := eulerFactor_prime_div_le_log hσ₂ hrp
  have hrew : ∀ s : ℝ, s ≠ 0 →
      s ^ (-(2 : ℤ)) * ((1 - (q : ℝ) ^ (-s)) * (1 - (r : ℝ) ^ (-s)))
      = ((1 - (q : ℝ) ^ (-s)) / s) * ((1 - (r : ℝ) ^ (-s)) / s) := by
    intro s hs
    rw [zpow_neg, zpow_two]
    field_simp [hs]
  rw [hrew σ₁ (ne_of_gt hσ₁), hrew σ₂ (ne_of_gt hσ₂)]
  have hprod1 : ((1 - (q : ℝ) ^ (-σ₁)) / σ₁) * ((1 - (r : ℝ) ^ (-σ₁)) / σ₁)
      ≤ Real.log (q : ℝ) * Real.log (r : ℝ) :=
    mul_le_mul hq1.2 hr1.2 hr1.1 (le_trans hq1.1 hq1.2)
  have hprod2 : 0 ≤ ((1 - (q : ℝ) ^ (-σ₂)) / σ₂) * ((1 - (r : ℝ) ^ (-σ₂)) / σ₂) :=
    mul_nonneg hq2.1 hr2.1
  linarith

/-- **Main Theorem A (Bilateral Prime-Free Sign-Separation Inequality)**:
For every `n ≥ 4` and every `0 < σ₁ ≤ σ₂ ≤ 1 / log n`,
`Ξ_n°(σ₁) - Ξ_n°(σ₂) ≤ R_pr(n) + P_pp_bilat(n)`. -/
theorem bilateral_mellin_euler_upper_bound {n : ℕ} (hn : 4 ≤ n)
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ ≤ σ₂) (hσ₂ : σ₂ ≤ 1 / Real.log (n : ℝ)) :
    bilateralXi n σ₁ - bilateralXi n σ₂
      ≤ goldbachPrimePairSum n + bilateralPrimePowerErr n := by
  classical
  have hσ₂_pos : 0 < σ₂ := lt_of_lt_of_le hσ₁ hσ₁₂
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  unfold bilateralXi bilateralEuler
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  -- Partition [2, n-2] into (ω(x)=1 ∧ ω(n-x)=1) vs composite pairs (ω(x)+ω(n-x) ≥ 3)
  let S := Finset.Icc 2 (n - 2)
  let P := fun x : ℕ => x.primeFactors.card = 1 ∧ (n - x).primeFactors.card = 1
  rw [← Finset.sum_filter_add_sum_filter_not S P]
  -- Step 1: Every composite pair contributes ≤ 0
  have hcomp_le : ∑ x ∈ S.filter (fun x => ¬P x),
      (σ₁ ^ (-(2 : ℤ)) * (eulerFactor σ₁ x * eulerFactor σ₁ (n - x))
        - σ₂ ^ (-(2 : ℤ)) * (eulerFactor σ₂ x * eulerFactor σ₂ (n - x))) ≤ 0 := by
    refine Finset.sum_nonpos ?_
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    have hx_ge2 : 2 ≤ x := hx.1.1
    have hnx_ge2 : 2 ≤ n - x := by omega
    have hcx : 1 ≤ x.primeFactors.card :=
      Finset.one_le_card.mpr (Nat.nonempty_primeFactors.mpr (by omega))
    have hcnx : 1 ≤ (n - x).primeFactors.card :=
      Finset.one_le_card.mpr (Nat.nonempty_primeFactors.mpr (by omega))
    have hsum_card : 3 ≤ x.primeFactors.card + (n - x).primeFactors.card := by
      by_contra hlt
      have : x.primeFactors.card = 1 ∧ (n - x).primeFactors.card = 1 := by omega
      exact hx.2 this
    -- Apply scaled_euler_prod_mono on s = x.primeFactors.disjSum (n-x).primeFactors
    let idx := x.primeFactors.disjSum (n - x).primeFactors
    let a : ℕ ⊕ ℕ → ℝ := Sum.elim (fun q => Real.log (q : ℝ)) (fun r => Real.log (r : ℝ))
    have ha_pos : ∀ i ∈ idx, 0 < a i := by
      intro i hi
      cases i with
      | inl q =>
        have hq : q ∈ x.primeFactors := by simpa [idx] using hi
        exact Real.log_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_lt)
      | inr r =>
        have hr : r ∈ (n - x).primeFactors := by simpa [idx] using hi
        exact Real.log_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hr).one_lt)
    have hidx_card : idx.card = x.primeFactors.card + (n - x).primeFactors.card :=
      Finset.card_disjSum _ _
    have hsum_a : ∑ i ∈ idx, a i
        = (∑ q ∈ x.primeFactors, Real.log (q : ℝ)) + (∑ r ∈ (n - x).primeFactors, Real.log (r : ℝ)) := by
      simp [idx, a, Finset.sum_disjSum]
    have hlogx : ∑ q ∈ x.primeFactors, Real.log (q : ℝ) ≤ Real.log (n : ℝ) :=
      le_trans (sum_log_primeFactors_le_log (by omega))
        (Real.log_le_log (by exact_mod_cast (by omega : 0 < x)) (by exact_mod_cast (by omega : x ≤ n)))
    have hlognx : ∑ r ∈ (n - x).primeFactors, Real.log (r : ℝ) ≤ Real.log (n : ℝ) :=
      le_trans (sum_log_primeFactors_le_log (by omega))
        (Real.log_le_log (by exact_mod_cast (by omega : 0 < n - x)) (by exact_mod_cast (by omega : n - x ≤ n)))
    have hbound : σ₂ * ∑ i ∈ idx, a i ≤ 2 * ((idx.card : ℝ) - (2 : ℝ)) := by
      have h1 : ∑ i ∈ idx, a i ≤ 2 * Real.log (n : ℝ) := by linarith
      have h2 : σ₂ * ∑ i ∈ idx, a i ≤ (1 / Real.log (n : ℝ)) * (2 * Real.log (n : ℝ)) := by
        exact mul_le_mul hσ₂ h1 (Finset.sum_nonneg (fun i hi => le_of_lt (ha_pos i hi)))
          (le_of_lt (one_div_pos.mpr hlogn_pos))
      have h3 : (1 / Real.log (n : ℝ)) * (2 * Real.log (n : ℝ)) = 2 := by
        field_simp [ne_of_gt hlogn_pos]
      have h4 : (3 : ℝ) ≤ (idx.card : ℝ) := by exact_mod_cast (hidx_card ▸ hsum_card)
      linarith
    have hmono := scaled_euler_prod_mono idx a ha_pos 2 hσ₁ hσ₁₂ hbound
    have hprod_eq : ∀ σ : ℝ,
        ∏ i ∈ idx, (1 - Real.exp (-σ * a i)) = eulerFactor σ x * eulerFactor σ (n - x) := by
      intro σ
      rw [eulerFactor_eq_exp_prod, eulerFactor_eq_exp_prod]
      simp [idx, a, Finset.prod_disjSum]
    rw [hprod_eq σ₁, hprod_eq σ₂] at hmono
    norm_num at hmono
    rw [zpow_neg, zpow_two, zpow_neg, zpow_two]
    simpa [sq] using sub_nonpos.mpr hmono
  -- Step 2: Split P into prime-prime pairs and proper prime-power pairs
  have hpp_le : ∑ x ∈ S.filter P,
      (σ₁ ^ (-(2 : ℤ)) * (eulerFactor σ₁ x * eulerFactor σ₁ (n - x))
        - σ₂ ^ (-(2 : ℤ)) * (eulerFactor σ₂ x * eulerFactor σ₂ (n - x)))
      ≤ goldbachPrimePairSum n + bilateralPrimePowerErr n := by
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
      ext x
      simp [P, Q, and_assoc]
    rw [hS1, hS2]
    unfold goldbachPrimePairSum bilateralPrimePowerErr
    apply add_le_add
    · refine Finset.sum_le_sum ?_
      intro x hx
      rw [Finset.mem_filter] at hx
      have hx1 : x.primeFactors.card = 1 := by rw [hx.2.1.primeFactors]; simp
      have hnx1 : (n - x).primeFactors.card = 1 := by rw [hx.2.2.primeFactors]; simp
      have hle := bilateral_pp_term_le hσ₁ hσ₂_pos hx1 hnx1
      simpa [hx.2.1.primeFactors, hx.2.2.primeFactors] using hle
    · refine Finset.sum_le_sum ?_
      intro x hx
      rw [Finset.mem_filter] at hx
      exact bilateral_pp_term_le hσ₁ hσ₂_pos hx.2.1 hx.2.2.1
  linarith

/-- **Main Theorem A' (Bilateral Prime-Free Strong Goldbach Criterion)**:
For every `n ≥ 4` and any `0 < σ₁ ≤ σ₂ ≤ 1 / log n`, if
`Ξ_n°(σ₁) - Ξ_n°(σ₂) > P_pp_bilat(n)`, then `n` is the sum of two primes. -/
theorem bilateral_mellin_euler_goldbach_criterion {n : ℕ} (hn : 4 ≤ n)
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ ≤ σ₂) (hσ₂ : σ₂ ≤ 1 / Real.log (n : ℝ))
    (hgt : bilateralPrimePowerErr n < bilateralXi n σ₁ - bilateralXi n σ₂) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  have hub := bilateral_mellin_euler_upper_bound hn hσ₁ hσ₁₂ hσ₂
  have hpos : 0 < goldbachPrimePairSum n := by linarith
  by_contra hno
  push Not at hno
  have hzero : goldbachPrimePairSum n = 0 := by
    unfold goldbachPrimePairSum
    refine Finset.sum_eq_zero ?_
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    exfalso
    exact hno x (n - x) hx.2.1 hx.2.2 (by omega)
  linarith

/-! ### Part 4: One-Sided Mellin–Euler Criterion for Strong Goldbach -/

/-- One-sided Mellin–Euler sum `G_n°(σ) = ∑_{p ∈ [2, n-2], p prime} log p * eulerFactor σ (n - p)`. -/
noncomputable def oneSidedEuler (n : ℕ) (σ : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 (n - 2)).filter Nat.Prime, Real.log (p : ℝ) * eulerFactor σ (n - p)

/-- Scaled one-sided function `Φ_n°(σ) = σ^(-1) * G_n°(σ)`. -/
noncomputable def oneSidedPhi (n : ℕ) (σ : ℝ) : ℝ :=
  σ ^ (-(1 : ℤ)) * oneSidedEuler n σ

/-- Shifted prime Chebyshev sum `θ_n°(d) = ∑_{p ∈ [2, n-2], p prime, d ∣ (n - p)} log p`. -/
noncomputable def shiftedTheta (n d : ℕ) : ℝ :=
  ∑ p ∈ ((Finset.Icc 2 (n - 2)).filter Nat.Prime).filter (fun p => d ∣ (n - p)), Real.log (p : ℝ)

/-- Exact divisor-sum identity `G_n°(σ) = ∑_{d=1}^{n-2} μ(d) d^(-σ) θ_n°(d)`. -/
theorem oneSidedEuler_eq_theta_sum (n : ℕ) (σ : ℝ) :
    oneSidedEuler n σ =
      ∑ d ∈ Finset.Icc 1 (n - 2), (μ d : ℝ) * (d : ℝ) ^ (-σ) * shiftedTheta n d := by
  classical
  unfold oneSidedEuler shiftedTheta
  have h1 : ∑ p ∈ (Finset.Icc 2 (n - 2)).filter Nat.Prime, Real.log (p : ℝ) * eulerFactor σ (n - p)
      = ∑ p ∈ (Finset.Icc 2 (n - 2)).filter Nat.Prime,
          ∑ d ∈ Finset.Icc 1 (n - 2),
            if d ∣ (n - p) then Real.log (p : ℝ) * ((μ d : ℝ) * (d : ℝ) ^ (-σ)) else 0 := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    have hnp_pos : 0 < n - p := by omega
    have hnp_le : n - p ≤ n - 2 := by omega
    rw [eulerFactor_eq_moebius_sum σ hnp_pos, Finset.mul_sum]
    have hsub : (n - p).divisors = (Finset.Icc 1 (n - 2)).filter (· ∣ (n - p)) := by
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · intro ⟨hd, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hd hnp_pos, le_trans (Nat.le_of_dvd hnp_pos hd) hnp_le⟩, hd⟩
      · intro ⟨_, hd⟩
        exact ⟨hd, ne_of_gt hnp_pos⟩
    rw [hsub, Finset.sum_filter]
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro d _
  rw [← Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro p _
  ring

/-- One-sided proper prime-power error sum: primes `p ∈ [2, n-2]` with `n - p = q^a` (`a ≥ 2`). -/
noncomputable def oneSidedPrimePowerErr (n : ℕ) : ℝ :=
  ∑ p ∈ ((Finset.Icc 2 (n - 2)).filter Nat.Prime).filter
      (fun p => (n - p).primeFactors.card = 1 ∧ ¬(n - p).Prime),
    Real.log (p : ℝ) * (∑ q ∈ (n - p).primeFactors, Real.log (q : ℝ))

/-- **Main Theorem B (One-Sided Mellin–Euler Sign-Separation Inequality)**:
For every `n ≥ 4` and every `0 < σ₁ ≤ σ₂ ≤ 2 / log n`,
`Φ_n°(σ₁) - Φ_n°(σ₂) ≤ R_pr(n) + P_pp_one(n)`. -/
theorem oneSided_mellin_euler_upper_bound {n : ℕ} (hn : 4 ≤ n)
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ ≤ σ₂) (hσ₂ : σ₂ ≤ 2 / Real.log (n : ℝ)) :
    oneSidedPhi n σ₁ - oneSidedPhi n σ₂
      ≤ goldbachPrimePairSum n + oneSidedPrimePowerErr n := by
  classical
  have hσ₂_pos : 0 < σ₂ := lt_of_lt_of_le hσ₁ hσ₁₂
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  unfold oneSidedPhi oneSidedEuler
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  let S := (Finset.Icc 2 (n - 2)).filter Nat.Prime
  let P := fun p : ℕ => (n - p).primeFactors.card = 1
  rw [← Finset.sum_filter_add_sum_filter_not S P]
  have hcomp_le : ∑ p ∈ S.filter (fun p => ¬P p),
      (σ₁ ^ (-(1 : ℤ)) * (Real.log (p : ℝ) * eulerFactor σ₁ (n - p))
        - σ₂ ^ (-(1 : ℤ)) * (Real.log (p : ℝ) * eulerFactor σ₂ (n - p))) ≤ 0 := by
    refine Finset.sum_nonpos ?_
    intro p hp
    rw [Finset.mem_filter] at hp
    have hp_mem := hp.1
    rw [Finset.mem_filter, Finset.mem_Icc] at hp_mem
    have hnp_ge2 : 2 ≤ n - p := by omega
    have hcard_ge1 : 1 ≤ (n - p).primeFactors.card :=
      Finset.one_le_card.mpr (Nat.nonempty_primeFactors.mpr (by omega))
    have hcard_ge2 : 2 ≤ (n - p).primeFactors.card := by
      have hne1 : (n - p).primeFactors.card ≠ 1 := hp.2
      omega
    have ha_pos : ∀ q ∈ (n - p).primeFactors, 0 < Real.log (q : ℝ) :=
      fun q hq => Real.log_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_lt)
    have hlognp : ∑ q ∈ (n - p).primeFactors, Real.log (q : ℝ) ≤ Real.log (n : ℝ) :=
      le_trans (sum_log_primeFactors_le_log (by omega))
        (Real.log_le_log (by exact_mod_cast (by omega : 0 < n - p)) (by exact_mod_cast (by omega : n - p ≤ n)))
    have hbound : σ₂ * ∑ q ∈ (n - p).primeFactors, Real.log (q : ℝ)
        ≤ 2 * (((n - p).primeFactors.card : ℝ) - ((1 : ℕ) : ℝ)) := by
      have h1 : σ₂ * ∑ q ∈ (n - p).primeFactors, Real.log (q : ℝ)
          ≤ (2 / Real.log (n : ℝ)) * Real.log (n : ℝ) :=
        mul_le_mul hσ₂ hlognp (Finset.sum_nonneg (fun q hq => le_of_lt (ha_pos q hq)))
          (le_of_lt (div_pos (by norm_num) hlogn_pos))
      have h2 : (2 / Real.log (n : ℝ)) * Real.log (n : ℝ) = 2 := by
        field_simp [ne_of_gt hlogn_pos]
      have h3 : (2 : ℝ) ≤ ((n - p).primeFactors.card : ℝ) := by exact_mod_cast hcard_ge2
      norm_num
      linarith
    have hmono := scaled_euler_prod_mono (n - p).primeFactors (fun q => Real.log (q : ℝ))
      ha_pos 1 hσ₁ hσ₁₂ hbound
    rw [← eulerFactor_eq_exp_prod σ₁ (n - p), ← eulerFactor_eq_exp_prod σ₂ (n - p)] at hmono
    norm_num at hmono
    have hlogp_nonneg : 0 ≤ Real.log (p : ℝ) :=
      le_of_lt (Real.log_pos (by exact_mod_cast hp_mem.2.one_lt))
    have hmul := mul_le_mul_of_nonneg_left hmono hlogp_nonneg
    have hlhs : σ₁ ^ (-(1 : ℤ)) * (Real.log (p : ℝ) * eulerFactor σ₁ (n - p))
        = Real.log (p : ℝ) * (σ₁⁻¹ * eulerFactor σ₁ (n - p)) := by rw [zpow_neg, zpow_one]; ring
    have hrhs : σ₂ ^ (-(1 : ℤ)) * (Real.log (p : ℝ) * eulerFactor σ₂ (n - p))
        = Real.log (p : ℝ) * (σ₂⁻¹ * eulerFactor σ₂ (n - p)) := by rw [zpow_neg, zpow_one]; ring
    linarith
  have hpp_le : ∑ p ∈ S.filter P,
      (σ₁ ^ (-(1 : ℤ)) * (Real.log (p : ℝ) * eulerFactor σ₁ (n - p))
        - σ₂ ^ (-(1 : ℤ)) * (Real.log (p : ℝ) * eulerFactor σ₂ (n - p)))
      ≤ goldbachPrimePairSum n + oneSidedPrimePowerErr n := by
    let Q := fun p : ℕ => (n - p).Prime
    rw [← Finset.sum_filter_add_sum_filter_not (S.filter P) Q]
    have hS1 : (S.filter P).filter Q = (Finset.Icc 2 (n - 2)).filter (fun p => p.Prime ∧ (n - p).Prime) := by
      ext p
      simp only [Finset.mem_filter, S, P, Q]
      constructor
      · intro ⟨⟨⟨hp1, hp2⟩, _⟩, hq⟩; exact ⟨hp1, hp2, hq⟩
      · intro ⟨hp1, hp2, hq⟩
        exact ⟨⟨⟨hp1, hp2⟩, by rw [hq.primeFactors]; simp⟩, hq⟩
    have hS2 : (S.filter P).filter (fun p => ¬Q p)
        = S.filter (fun p => (n - p).primeFactors.card = 1 ∧ ¬(n - p).Prime) := by
      ext p
      simp [P, Q, and_assoc]
    rw [hS1, hS2]
    unfold goldbachPrimePairSum oneSidedPrimePowerErr
    have hterm_pp : ∀ p : ℕ, p.Prime → (n - p).primeFactors.card = 1 →
        σ₁ ^ (-(1 : ℤ)) * (Real.log (p : ℝ) * eulerFactor σ₁ (n - p))
          - σ₂ ^ (-(1 : ℤ)) * (Real.log (p : ℝ) * eulerFactor σ₂ (n - p))
        ≤ Real.log (p : ℝ) * (∑ q ∈ (n - p).primeFactors, Real.log (q : ℝ)) := by
      intro p hp hc1
      obtain ⟨q, hq_eq⟩ := Finset.card_eq_one.mp hc1
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors (by rw [hq_eq]; simp)
      simp only [eulerFactor, hq_eq, Finset.prod_singleton, Finset.sum_singleton]
      have hq1 := eulerFactor_prime_div_le_log hσ₁ hqp
      have hq2 := eulerFactor_prime_div_le_log hσ₂_pos hqp
      have hlogp : 0 ≤ Real.log (p : ℝ) := le_of_lt (Real.log_pos (by exact_mod_cast hp.one_lt))
      have hrew : ∀ s : ℝ, s ≠ 0 →
          s ^ (-(1 : ℤ)) * (Real.log (p : ℝ) * (1 - (q : ℝ) ^ (-s)))
          = Real.log (p : ℝ) * ((1 - (q : ℝ) ^ (-s)) / s) := by
        intro s hs; rw [zpow_neg, zpow_one]; field_simp [hs]
      rw [hrew σ₁ (ne_of_gt hσ₁), hrew σ₂ (ne_of_gt hσ₂_pos)]
      have hsub : (1 - (q : ℝ) ^ (-σ₁)) / σ₁ - (1 - (q : ℝ) ^ (-σ₂)) / σ₂ ≤ Real.log (q : ℝ) := by
        linarith
      calc Real.log (p : ℝ) * ((1 - (q : ℝ) ^ (-σ₁)) / σ₁)
            - Real.log (p : ℝ) * ((1 - (q : ℝ) ^ (-σ₂)) / σ₂)
          = Real.log (p : ℝ) * ((1 - (q : ℝ) ^ (-σ₁)) / σ₁ - (1 - (q : ℝ) ^ (-σ₂)) / σ₂) := by ring
        _ ≤ Real.log (p : ℝ) * Real.log (q : ℝ) := mul_le_mul_of_nonneg_left hsub hlogp
    apply add_le_add
    · refine Finset.sum_le_sum ?_
      intro p hp
      rw [Finset.mem_filter] at hp
      have hc1 : (n - p).primeFactors.card = 1 := by rw [hp.2.2.primeFactors]; simp
      simpa [hp.2.2.primeFactors] using hterm_pp p hp.2.1 hc1
    · refine Finset.sum_le_sum ?_
      intro p hp
      rw [Finset.mem_filter] at hp
      have hp_mem := hp.1
      rw [Finset.mem_filter] at hp_mem
      exact hterm_pp p hp_mem.2 hp.2.1
  linarith

/-- **Main Theorem B' (One-Sided Mellin–Euler Strong Goldbach Criterion)**:
For every `n ≥ 4` and any `0 < σ₁ ≤ σ₂ ≤ 2 / log n`, if
`Φ_n°(σ₁) - Φ_n°(σ₂) > P_pp_one(n)`, then `n` is the sum of two primes. -/
theorem oneSided_mellin_euler_goldbach_criterion {n : ℕ} (hn : 4 ≤ n)
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ ≤ σ₂) (hσ₂ : σ₂ ≤ 2 / Real.log (n : ℝ))
    (hgt : oneSidedPrimePowerErr n < oneSidedPhi n σ₁ - oneSidedPhi n σ₂) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  have hub := oneSided_mellin_euler_upper_bound hn hσ₁ hσ₁₂ hσ₂
  have hpos : 0 < goldbachPrimePairSum n := by linarith
  by_contra hno
  push Not at hno
  have hzero : goldbachPrimePairSum n = 0 := by
    unfold goldbachPrimePairSum
    refine Finset.sum_eq_zero ?_
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    exfalso
    exact hno x (n - x) hx.2.1 hx.2.2 (by omega)
  linarith

end GoldbachAttack

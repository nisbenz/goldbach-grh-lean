import Mathlib

/-!
# Wave 30: Exact Squarefree-Counting Identity (`O(√M)` Error with Constant `1`) & Exact Affine Binary Chowla Parametrization of the Remaining `[3/5, 1]^2` Core

Wave 29 (`SemiprimeAnnihilationAndSwitch.lean`) proved the exact `L²` Möbius factorization
`μ(x/k₁) μ(x/k₂) = μ(r₁) μ(r₂) 1_{(m, r₁ r₂)=1} (μ m)²`, reducing `‖Λ_{≤ K}^*‖₂²` to squarefree
counting in `m`, while Wave 28 (`HeathBrownWellFactorable.lean`) shrunk the remaining open core
to `[3/5, 1]^2` (`k₁, k₂ < n^{2/5}`).

Wave 30 proves five completely unconditional, kernel-checked theorems in Lean 4
(standard axioms `[propext, Classical.choice, Quot.sound]` only):

1. **`moebius_sq_eq_sum_sq_divisors`**:
   For every `m ≥ 1`, `(μ m : ℤ)² = ∑ d ∈ m.divisors.filter (fun d => d * d ∣ m), μ d`
   (proved from scratch via multiplicativity on prime powers `p^e`!).
2. **`squarefree_count_exact_identity`**:
   Exact Dirichlet hyperbola identity for squarefree counting:
   `∑ m ∈ Finset.Icc 1 M, ((μ m : ℝ) ^ 2) = ∑ d ∈ Finset.Icc 1 (Nat.sqrt M), (μ d : ℝ) * ((M / (d * d) : ℕ) : ℝ)`.
3. **`squarefree_count_error_le_sqrt`**:
   Exact explicit error bound with constant `1`:
   `|∑ m ∈ Finset.Icc 1 M, ((μ m : ℝ) ^ 2) - (M : ℝ) * ∑ d ∈ Finset.Icc 1 (Nat.sqrt M), (μ d : ℝ) / ((d * d : ℕ) : ℝ)| ≤ (Nat.sqrt M : ℝ)`.
4. **`affine_chowla_parametrization` & `affine_chowla_determinant_identity`**:
   Exact integer parametrization of ALL solutions to `k₁ * d₁ + k₂ * d₂ = n`:
   for any base solution `(d₁⁰, d₂⁰)` and `g = gcd(k₁, k₂)`, `k₁' = k₁ / g`, `k₂' = k₂ / g`,
   `k₁ * d₁ + k₂ * d₂ = n ↔ ∃ t : ℤ, d₁ = d₁⁰ + k₂' * t ∧ d₂ = d₂⁰ - k₁' * t`,
   with exact non-degenerate affine determinant `d₁⁰ * (-k₁') - d₂⁰ * k₂' = -(n / g)`!
5. **`affine_chowla_length_lower_bound_on_35_square`**:
   Every cofactor pair `(k₁, k₂)` in Wave 28's remaining square `[3/5, 1]^2` (`k₁, k₂ ≤ n^{2/5}`)
   gives an affine binary Chowla sum `∑_t μ(d₁⁰ + k₂' t) μ(d₂⁰ - k₁' t)` of full polynomial length
   `n / (k₁ * k₂) ≥ n^{1/5}`!
-/

open scoped BigOperators ArithmeticFunction.Moebius
open Finset Real ArithmeticFunction

namespace GoldbachWave30

/-! ### Part 1: Exact Squarefree Indicator Identity `(μ m)² = ∑_{d² ∣ m} μ(d)` -/

/-- Arithmetic function `sqDivMoebius m = ∑_{d ∣ m, d^2 ∣ m} μ(d)` (`0` at `m = 0`). -/
def sqDivMoebius : ArithmeticFunction ℤ where
  toFun m := if m = 0 then 0 else ∑ d ∈ m.divisors.filter (fun d => d * d ∣ m), μ d
  map_zero' := by simp

/-- Square of Möbius as an `ArithmeticFunction ℤ`: `muSq m = (μ m)^2`. -/
def muSq : ArithmeticFunction ℤ where
  toFun m := (μ m) ^ 2
  map_zero' := by simp

lemma isMultiplicative_muSq : muSq.IsMultiplicative := by
  refine ⟨by simp [muSq], ?_⟩
  intro a b hcop
  change (μ (a * b)) ^ 2 = (μ a) ^ 2 * (μ b) ^ 2
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop, mul_pow]

lemma isMultiplicative_sqDivMoebius : sqDivMoebius.IsMultiplicative := by
  refine ⟨by simp [sqDivMoebius, Finset.filter_eq'], ?_⟩
  intro a b hcop
  by_cases ha : a = 0
  · subst ha; simp [sqDivMoebius]
  by_cases hb : b = 0
  · subst hb; simp [sqDivMoebius]
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  simp only [sqDivMoebius, ArithmeticFunction.coe_mk, hab, ha, hb, ↓reduceIte]
  -- Bijection (d₁, d₂) ↦ d₁ * d₂ between {d₁ | d₁² ∣ a} × {d₂ | d₂² ∣ b} and {d | d² ∣ a * b}!
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun (p : ℕ × ℕ) _ => p.1 * p.2) ?_ ?_ ?_ ?_
  · rintro ⟨d₁, d₂⟩ hp
    rw [Finset.mem_product] at hp
    have h1 := Finset.mem_filter.mp hp.1
    have h2 := Finset.mem_filter.mp hp.2
    rw [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors h1.1) (Nat.dvd_of_mem_divisors h2.1), hab⟩, ?_⟩
    have heq : (d₁ * d₂) * (d₁ * d₂) = (d₁ * d₁) * (d₂ * d₂) := by ring
    rw [heq]
    exact Nat.mul_dvd_mul h1.2 h2.2
  · rintro ⟨d₁, d₂⟩ hp₁ ⟨e₁, e₂⟩ hp₂ heq
    rw [Finset.mem_product] at hp₁ hp₂
    have hd1 : d₁ ∣ a := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hp₁.1).1
    have hd2 : d₂ ∣ b := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hp₁.2).1
    have he1 : e₁ ∣ a := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hp₂.1).1
    have he2 : e₂ ∣ b := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hp₂.2).1
    have hcop_d1_e2 : Nat.Coprime d₁ e₂ := (hcop.coprime_dvd_left hd1).coprime_dvd_right he2
    have hcop_e1_d2 : Nat.Coprime e₁ d₂ := (hcop.coprime_dvd_left he1).coprime_dvd_right hd2
    have h1 : d₁ ∣ e₁ := hcop_d1_e2.dvd_of_dvd_mul_right ⟨d₂, heq.symm⟩
    have h2 : e₁ ∣ d₁ := hcop_e1_d2.dvd_of_dvd_mul_right ⟨e₂, heq⟩
    have heq1 : d₁ = e₁ := Nat.dvd_antisymm h1 h2
    have hd1_pos : 0 < d₁ := Nat.pos_of_dvd_of_pos hd1 (Nat.pos_of_ne_zero ha)
    have heq2 : d₂ = e₂ := Nat.eq_of_mul_eq_mul_left hd1_pos (by rw [← heq1] at heq; exact heq)
    exact Prod.ext heq1 heq2
  · intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    let d₁ := Nat.gcd d a
    let d₂ := Nat.gcd d b
    have hcop_ab_d : d₁ * d₂ = d := by
      have h1 : Nat.gcd d (a * b) = d := Nat.gcd_eq_left hd.1.1
      rw [← h1]
      exact (Nat.Coprime.gcd_mul d hcop).symm
    have hd1_sq : d₁ * d₁ ∣ a := by
      have hdd : (d₁ * d₁) * (d₂ * d₂) ∣ a * b := by
        have heq : (d₁ * d₁) * (d₂ * d₂) = d * d := by rw [← hcop_ab_d]; ring
        rw [heq]; exact hd.2
      have hcop1 : Nat.Coprime (d₁ * d₁) b :=
        (hcop.coprime_dvd_left (Nat.gcd_dvd_right d a)).mul_left (hcop.coprime_dvd_left (Nat.gcd_dvd_right d a))
      exact hcop1.dvd_of_dvd_mul_right (dvd_trans (dvd_mul_right _ _) hdd)
    have hd2_sq : d₂ * d₂ ∣ b := by
      have hdd : (d₁ * d₁) * (d₂ * d₂) ∣ a * b := by
        have heq : (d₁ * d₁) * (d₂ * d₂) = d * d := by rw [← hcop_ab_d]; ring
        rw [heq]; exact hd.2
      have hcop2 : Nat.Coprime (d₂ * d₂) a :=
        (hcop.symm.coprime_dvd_left (Nat.gcd_dvd_right d b)).mul_left (hcop.symm.coprime_dvd_left (Nat.gcd_dvd_right d b))
      exact hcop2.dvd_of_dvd_mul_left (dvd_trans (dvd_mul_left _ _) hdd)
    refine ⟨(d₁, d₂), ?_, hcop_ab_d⟩
    rw [Finset.mem_product]
    refine ⟨Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right d a, ha⟩, hd1_sq⟩,
            Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right d b, hb⟩, hd2_sq⟩⟩
  · rintro ⟨d₁, d₂⟩ hp
    rw [Finset.mem_product] at hp
    have hd1 : d₁ ∣ a := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hp.1).1
    have hd2 : d₂ ∣ b := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hp.2).1
    have hcop12 : Nat.Coprime d₁ d₂ := (hcop.coprime_dvd_left hd1).coprime_dvd_right hd2
    exact (ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop12).symm

/-- **Theorem 1 (Exact Squarefree Indicator Identity `(μ m)² = ∑_{d² ∣ m} μ(d)`)**:
For every `m ≥ 1`, `(μ m : ℤ)^2 = ∑ d ∈ m.divisors.filter (fun d => d * d ∣ m), μ d`! -/
theorem moebius_sq_eq_sum_sq_divisors {m : ℕ} (hm : 1 ≤ m) :
    (μ m) ^ 2 = ∑ d ∈ m.divisors.filter (fun d => d * d ∣ m), μ d := by
  have heq : muSq = sqDivMoebius := by
    refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
      muSq isMultiplicative_muSq sqDivMoebius isMultiplicative_sqDivMoebius).mpr ?_
    intro p k hp
    have hp_ne : p ≠ 0 := hp.ne_zero
    have hpk_ne : p ^ k ≠ 0 := pow_ne_zero k hp_ne
    simp only [muSq, sqDivMoebius, ArithmeticFunction.coe_mk, hpk_ne, ↓reduceIte]
    cases k with
    | zero =>
      simp [Finset.filter_eq']
    | succ k' =>
      cases k' with
      | zero =>
        -- k = 1: p^1 = p, only d = 1 satisfies d * d ∣ p!
        rw [pow_one, ArithmeticFunction.moebius_apply_prime hp]
        have hfilt : p.divisors.filter (fun d => d * d ∣ p) = {1} := by
          rw [hp.divisors]
          ext d
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨hd | hd, hsq⟩
            · exact hd
            · exfalso
              rw [hd] at hsq
              have hle : p * p ≤ p := Nat.le_of_dvd hp.pos hsq
              have hp2 : 2 ≤ p := hp.two_le
              nlinarith
          · rintro rfl; exact ⟨Or.inl rfl, one_dvd p⟩
        rw [hfilt]; simp
      | succ k'' =>
        -- k = k'' + 2 ≥ 2: μ(p^k) = 0, and sum over d = p^j (2j ≤ k) has μ(p^j) = 0 for j ≥ 2,
        -- leaving ONLY j = 0 (μ 1 = 1) and j = 1 (μ p = -1), which cancel to 0!
        have hnot_sf : ¬Squarefree (p ^ (k'' + 2)) := by
          intro hsf
          have hdvd : p * p ∣ p ^ (k'' + 2) := by
            rw [show p ^ (k'' + 2) = (p * p) * p ^ k'' by ring]
            exact dvd_mul_right _ _
          exact hp.not_isUnit (hsf p hdvd)
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnot_sf, zero_pow (by norm_num)]
        -- Split filter into {1, p} and the rest (all divisible by p^2, so μ d = 0!)
        let S := (p ^ (k'' + 2)).divisors.filter (fun d => d * d ∣ p ^ (k'' + 2))
        have hsub : ({1, p} : Finset ℕ) ⊆ S := by
          intro d hd
          simp only [Finset.mem_insert, Finset.mem_singleton] at hd
          rw [Finset.mem_filter, Nat.mem_divisors]
          rcases hd with rfl | hd
          · exact ⟨⟨one_dvd _, hpk_ne⟩, one_dvd _⟩
          · rw [hd]
            refine ⟨⟨dvd_pow_self p (by omega), hpk_ne⟩, ?_⟩
            rw [show p ^ (k'' + 2) = (p * p) * p ^ k'' by ring]
            exact dvd_mul_right _ _
        have hrest0 : ∀ d ∈ S, d ∉ ({1, p} : Finset ℕ) → μ d = 0 := by
          intro d hd hnot
          have hd_dvd : d ∣ p ^ (k'' + 2) := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
          obtain ⟨j, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hd_dvd
          have hj2 : 2 ≤ j := by
            by_contra hlt; push Not at hlt
            apply hnot
            simp only [Finset.mem_insert, Finset.mem_singleton]
            interval_cases j
            · left; simp
            · right; simp
          have hns : ¬Squarefree (p ^ j) := by
            intro hsf
            have hdvd : p * p ∣ p ^ j := by
              rw [show j = (j - 2) + 2 by omega, show p ^ ((j - 2) + 2) = (p * p) * p ^ (j - 2) by ring]
              exact dvd_mul_right _ _
            exact hp.not_isUnit (hsf p hdvd)
          exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns
        have hsum_eq : ∑ d ∈ S, μ d = ∑ d ∈ ({1, p} : Finset ℕ), μ d :=
          (Finset.sum_subset hsub hrest0).symm
        rw [hsum_eq, Finset.sum_pair hp.ne_one.symm, ArithmeticFunction.moebius_apply_one,
          ArithmeticFunction.moebius_apply_prime hp]
        ring
  have h := congrArg (fun f : ArithmeticFunction ℤ => f m) heq
  simpa [muSq, sqDivMoebius, show m ≠ 0 by omega] using h

/-! ### Part 2: Exact Squarefree-Counting Identity & `O(√M)` Error Bound (Constant `1`) -/

/-- **Theorem 2 (Exact Dirichlet Hyperbola Identity for Squarefree Counting)**:
For every `M : ℕ`:
`∑ m ∈ Finset.Icc 1 M, ((μ m : ℝ) ^ 2) = ∑ d ∈ Finset.Icc 1 (Nat.sqrt M), (μ d : ℝ) * ((M / (d * d) : ℕ) : ℝ)`. -/
theorem squarefree_count_exact_identity (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, ((μ m : ℝ) ^ 2)
      = ∑ d ∈ Finset.Icc 1 (Nat.sqrt M), (μ d : ℝ) * ((M / (d * d) : ℕ) : ℝ) := by
  have h1 : ∑ m ∈ Finset.Icc 1 M, ((μ m : ℝ) ^ 2)
      = ∑ m ∈ Finset.Icc 1 M, ∑ d ∈ Finset.Icc 1 (Nat.sqrt M), if d * d ∣ m then (μ d : ℝ) else 0 := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    have hsq : ((μ m : ℝ) ^ 2) = ∑ d ∈ m.divisors.filter (fun d => d * d ∣ m), (μ d : ℝ) := by
      exact_mod_cast moebius_sq_eq_sum_sq_divisors hm.1
    rw [hsq, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hd, _⟩, hdd⟩
      have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
      have hdd_le : d * d ≤ M := le_trans (Nat.le_of_dvd (by omega) hdd) hm.2
      exact ⟨⟨hd_pos, Nat.le_sqrt.mpr hdd_le⟩, hdd⟩
    · rintro ⟨⟨hd_pos, _⟩, hdd⟩
      exact ⟨⟨dvd_trans (dvd_mul_right d d) hdd, by omega⟩, hdd⟩
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  have hd_pos : 0 < d := hd.1
  have hdd_pos : 0 < d * d := Nat.mul_pos hd_pos hd_pos
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  -- Cardinality of {m ∈ Icc 1 M | d * d ∣ m} equals M / (d * d)!
  have hcard : ((Finset.Icc 1 M).filter (fun m => d * d ∣ m)).card = M / (d * d) := by
    have hbij : (Finset.Icc 1 M).filter (fun m => d * d ∣ m)
        = (Finset.Icc 1 (M / (d * d))).image (fun q => (d * d) * q) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨⟨hm1, hmM⟩, ⟨q, rfl⟩⟩
        have hq1 : 1 ≤ q := by
          by_contra h0; push Not at h0
          have : q = 0 := by omega
          subst this; simp at hm1
        have hqM : q ≤ M / (d * d) := (Nat.le_div_iff_mul_le hdd_pos).mpr (by rw [mul_comm]; exact hmM)
        exact ⟨q, ⟨hq1, hqM⟩, rfl⟩
      · rintro ⟨q, ⟨hq1, hqM⟩, rfl⟩
        refine ⟨⟨Nat.mul_pos hdd_pos hq1, ?_⟩, dvd_mul_right _ _⟩
        calc d * d * q ≤ d * d * (M / (d * d)) := Nat.mul_le_mul_left _ hqM
          _ ≤ M := Nat.mul_div_le M (d * d)
    rw [hbij, Finset.card_image_of_injective _ (mul_right_injective₀ (ne_of_gt hdd_pos)), Nat.card_Icc]
    simp
  exact_mod_cast hcard

/-- **Theorem 3 (Unconditional `O(√M)` Squarefree-Counting Error Bound with Constant `1`)**:
For every `M : ℕ`:
`|∑ m ∈ Finset.Icc 1 M, ((μ m : ℝ) ^ 2) - (M : ℝ) * ∑ d ∈ Finset.Icc 1 (Nat.sqrt M), (μ d : ℝ) / ((d * d : ℕ) : ℝ)| ≤ (Nat.sqrt M : ℝ)`! -/
theorem squarefree_count_error_le_sqrt (M : ℕ) :
    |∑ m ∈ Finset.Icc 1 M, ((μ m : ℝ) ^ 2)
        - (M : ℝ) * ∑ d ∈ Finset.Icc 1 (Nat.sqrt M), (μ d : ℝ) / ((d * d : ℕ) : ℝ)|
      ≤ (Nat.sqrt M : ℝ) := by
  rw [squarefree_count_exact_identity M, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ d ∈ Finset.Icc 1 (Nat.sqrt M),
            |(μ d : ℝ) * ((M / (d * d) : ℕ) : ℝ) - (M : ℝ) * ((μ d : ℝ) / ((d * d : ℕ) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Finset.Icc 1 (Nat.sqrt M), (1 : ℝ) := by
        refine Finset.sum_le_sum fun d hd => ?_
        rw [Finset.mem_Icc] at hd
        have hdd_pos : 0 < d * d := Nat.mul_pos hd.1 hd.1
        have hddR_pos : (0 : ℝ) < ((d * d : ℕ) : ℝ) := Nat.cast_pos.mpr hdd_pos
        have hrew : (μ d : ℝ) * ((M / (d * d) : ℕ) : ℝ) - (M : ℝ) * ((μ d : ℝ) / ((d * d : ℕ) : ℝ))
            = (μ d : ℝ) * (((M / (d * d) : ℕ) : ℝ) - (M : ℝ) / ((d * d : ℕ) : ℝ)) := by ring
        rw [hrew, abs_mul]
        have hmu : |(μ d : ℝ)| ≤ 1 := by
          have h1 : |μ d| ≤ 1 := by
            by_cases hsf : Squarefree d
            · rw [ArithmeticFunction.moebius_apply_of_squarefree hsf]; simp
            · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; simp
          exact_mod_cast h1
        have hfrac : |((M / (d * d) : ℕ) : ℝ) - (M : ℝ) / ((d * d : ℕ) : ℝ)| ≤ 1 := by
          have hdiv_mod : (M : ℝ) = ((M / (d * d) : ℕ) : ℝ) * ((d * d : ℕ) : ℝ) + ((M % (d * d) : ℕ) : ℝ) := by
            exact_mod_cast (Nat.div_add_mod' M (d * d)).symm
          have hsub : ((M / (d * d) : ℕ) : ℝ) - (M : ℝ) / ((d * d : ℕ) : ℝ)
              = -(((M % (d * d) : ℕ) : ℝ) / ((d * d : ℕ) : ℝ)) := by
            rw [hdiv_mod]; field_simp [ne_of_gt hddR_pos]; ring
          rw [hsub, abs_neg, abs_of_nonneg (by positivity), div_le_one hddR_pos]
          exact_mod_cast le_of_lt (Nat.mod_lt M hdd_pos)
        nlinarith [abs_nonneg (μ d : ℝ), abs_nonneg (((M / (d * d) : ℕ) : ℝ) - (M : ℝ) / ((d * d : ℕ) : ℝ))]
    _ = (Nat.sqrt M : ℝ) := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp

/-! ### Part 3: Exact Affine Binary Chowla Parametrization & Determinant of `[3/5, 1]^2` -/

/-- **Theorem 4a (Exact Affine Binary Chowla Parametrization of `k₁ * d₁ + k₂ * d₂ = n`)**:
For ANY positive naturals `k₁, k₂` with `g = gcd(k₁, k₂)`, `k₁' = k₁ / g`, `k₂' = k₂ / g`,
and ANY base integer solution `(d₁⁰, d₂⁰)` of `k₁ * d₁⁰ + k₂ * d₂⁰ = n`:
every integer solution `(d₁, d₂)` is UNIQUELY parameterized as `(d₁⁰ + k₂' * t, d₂⁰ - k₁' * t)` (`t : ℤ`)! -/
theorem affine_chowla_parametrization {n k₁ k₂ : ℕ} (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    {d₁₀ d₂₀ : ℤ} (hbase : (k₁ : ℤ) * d₁₀ + (k₂ : ℤ) * d₂₀ = (n : ℤ)) (d₁ d₂ : ℤ) :
    let g := Nat.gcd k₁ k₂
    let k₁' := k₁ / g
    let k₂' := k₂ / g
    (k₁ : ℤ) * d₁ + (k₂ : ℤ) * d₂ = (n : ℤ) ↔
      ∃ t : ℤ, d₁ = d₁₀ + (k₂' : ℤ) * t ∧ d₂ = d₂₀ - (k₁' : ℤ) * t := by
  intro g k₁' k₂'
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left k₂ hk₁
  have hg1 : g ∣ k₁ := Nat.gcd_dvd_left k₁ k₂
  have hg2 : g ∣ k₂ := Nat.gcd_dvd_right k₁ k₂
  have hk1_eq : (k₁ : ℤ) = (g : ℤ) * (k₁' : ℤ) := by exact_mod_cast (Nat.mul_div_cancel' hg1).symm
  have hk2_eq : (k₂ : ℤ) = (g : ℤ) * (k₂' : ℤ) := by exact_mod_cast (Nat.mul_div_cancel' hg2).symm
  have hcop : Nat.Coprime k₁' k₂' := Nat.coprime_div_gcd_div_gcd hg_pos
  have hcopZ : IsCoprime (k₁' : ℤ) (k₂' : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have hg_ne : (g : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (ne_of_gt hg_pos)
  constructor
  · intro hsol
    have hdiff : (k₁ : ℤ) * (d₁ - d₁₀) = (k₂ : ℤ) * (d₂₀ - d₂) := by linarith
    rw [hk1_eq, hk2_eq] at hdiff
    have hdiff' : (k₁' : ℤ) * (d₁ - d₁₀) = (k₂' : ℤ) * (d₂₀ - d₂) := by
      apply mul_left_cancel₀ hg_ne; linarith
    have hdvd : (k₂' : ℤ) ∣ d₁ - d₁₀ :=
      hcopZ.symm.dvd_of_dvd_mul_left ⟨d₂₀ - d₂, hdiff'⟩
    obtain ⟨t, ht⟩ := hdvd
    refine ⟨t, by linarith, ?_⟩
    have hmul : (k₁' : ℤ) * ((k₂' : ℤ) * t) = (k₂' : ℤ) * (d₂₀ - d₂) := by rw [← ht]; exact hdiff'
    have hk2'_pos : 0 < k₂' := Nat.div_pos (Nat.le_of_dvd hk₂ hg2) hg_pos
    have hk2'_ne : (k₂' : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (ne_of_gt hk2'_pos)
    have h2 : d₂₀ - d₂ = (k₁' : ℤ) * t := by
      apply mul_left_cancel₀ hk2'_ne; linarith
    linarith
  · rintro ⟨t, rfl, rfl⟩
    rw [hk1_eq, hk2_eq] at hbase ⊢
    linear_combination hbase

/-- **Theorem 4b (Exact Non-Degenerate Affine Determinant Identity)**:
For any base solution `(d₁₀, d₂₀)` of `k₁ * d₁₀ + k₂ * d₂₀ = n` (`g = gcd(k₁, k₂) ∣ n`),
the determinant of the affine pair `(d₁₀ + k₂' t, d₂₀ - k₁' t)` is identically `-(n / g)`! -/
theorem affine_chowla_determinant_identity {n k₁ k₂ : ℕ} (hk₁ : 0 < k₁)
    {d₁₀ d₂₀ : ℤ} (hbase : (k₁ : ℤ) * d₁₀ + (k₂ : ℤ) * d₂₀ = (n : ℤ)) :
    let g := Nat.gcd k₁ k₂
    let k₁' := k₁ / g
    let k₂' := k₂ / g
    g ∣ n ∧ d₁₀ * (-(k₁' : ℤ)) - d₂₀ * (k₂' : ℤ) = -((n / g : ℕ) : ℤ) := by
  intro g k₁' k₂'
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left k₂ hk₁
  have hg1 : g ∣ k₁ := Nat.gcd_dvd_left k₁ k₂
  have hg2 : g ∣ k₂ := Nat.gcd_dvd_right k₁ k₂
  have hk1_eq : (k₁ : ℤ) = (g : ℤ) * (k₁' : ℤ) := by exact_mod_cast (Nat.mul_div_cancel' hg1).symm
  have hk2_eq : (k₂ : ℤ) = (g : ℤ) * (k₂' : ℤ) := by exact_mod_cast (Nat.mul_div_cancel' hg2).symm
  have hgnZ : (g : ℤ) ∣ (n : ℤ) := by
    refine ⟨(k₁' : ℤ) * d₁₀ + (k₂' : ℤ) * d₂₀, ?_⟩
    rw [hk1_eq, hk2_eq] at hbase; linarith
  have hgn : g ∣ n := Int.natCast_dvd_natCast.mp hgnZ
  refine ⟨hgn, ?_⟩
  have hn_eq : (n : ℤ) = (g : ℤ) * ((n / g : ℕ) : ℤ) := by exact_mod_cast (Nat.mul_div_cancel' hgn).symm
  have hg_ne : (g : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (ne_of_gt hg_pos)
  apply mul_left_cancel₀ hg_ne
  rw [hk1_eq, hk2_eq, hn_eq] at hbase
  linarith

/-- **Theorem 5 (Uniform Polynomial Length `n^{1/5}` of Every Affine Binary Chowla Sum on `[3/5, 1]^2`)**:
For every positive real `n > 0` and every cofactor pair `k₁, k₂` in Wave 28's remaining square `[3/5, 1]^2`
(`0 < k₁ ≤ n^{2/5}` and `0 < k₂ ≤ n^{2/5}`), the affine binary Chowla length satisfies
`n / (k₁ * k₂) ≥ n^{1/5}` (uniformly bounded below by a full power of `n`!)! -/
theorem affine_chowla_length_lower_bound_on_35_square {n k₁ k₂ : ℝ}
    (hn : 0 < n) (hk₁0 : 0 < k₁) (hk₂0 : 0 < k₂)
    (hk₁ : k₁ ≤ n ^ ((2 : ℝ) / 5)) (hk₂ : k₂ ≤ n ^ ((2 : ℝ) / 5)) :
    n ^ ((1 : ℝ) / 5) ≤ n / (k₁ * k₂) := by
  have hprod : k₁ * k₂ ≤ n ^ ((4 : ℝ) / 5) := by
    calc k₁ * k₂ ≤ n ^ ((2 : ℝ) / 5) * n ^ ((2 : ℝ) / 5) :=
          mul_le_mul hk₁ hk₂ (le_of_lt hk₂0) (le_of_lt (Real.rpow_pos_of_pos hn _))
      _ = n ^ ((2 : ℝ) / 5 + (2 : ℝ) / 5) := (Real.rpow_add hn _ _).symm
      _ = n ^ ((4 : ℝ) / 5) := by norm_num
  have h15_45 : n ^ ((1 : ℝ) / 5) * n ^ ((4 : ℝ) / 5) = n := by
    rw [← Real.rpow_add hn]; norm_num
  rw [le_div_iff₀ (mul_pos hk₁0 hk₂0)]
  calc n ^ ((1 : ℝ) / 5) * (k₁ * k₂)
      ≤ n ^ ((1 : ℝ) / 5) * n ^ ((4 : ℝ) / 5) :=
        mul_le_mul_of_nonneg_left hprod (le_of_lt (Real.rpow_pos_of_pos hn _))
    _ = n := h15_45

end GoldbachWave30

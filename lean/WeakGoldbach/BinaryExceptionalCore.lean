import WeakGoldbach.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace WeakGoldbach

/-- The Binary (Strong) Goldbach exceptional set up to `X`:
    all even integers `n ∈ [4, X]` that are NOT the sum of two primes. -/
noncomputable def binaryExceptionalSet (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 4 X).filter (fun n => Even n ∧ ¬ IsSumOfTwoPrimes n)

/-- Cardinality `E(X)` of the Binary Goldbach exceptional set up to `X`. -/
noncomputable def binaryExceptionalCount (X : ℕ) : ℕ :=
  (binaryExceptionalSet X).card

/-- Dyadic slice of the Binary Goldbach exceptional set on `(X / 2, X]`. -/
noncomputable def dyadicExceptionalSet (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc (X / 2) X).filter (fun n => 4 ≤ n ∧ Even n ∧ ¬ IsSumOfTwoPrimes n)

/-- Weighted strictly-prime binary Goldbach representation count
    `R2_prime(X, n) = e^(-n/X) ∑_{p₁ + p₂ = n} log p₁ log p₂`. -/
noncomputable def R2_prime (X : ℝ) (n : ℕ) : ℝ :=
  ∑ p₁ ∈ Finset.range (n + 1),
    ∑ p₂ ∈ Finset.range (n + 1),
      if Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ p₁ + p₂ = n then
        Real.exp (-(n : ℝ) / X) * Real.log p₁ * Real.log p₂
      else 0

/-- If `R2_prime X n > 0`, then `n` is a sum of two primes. -/
theorem isSumOfTwoPrimes_of_R2_prime_pos {X : ℝ} {n : ℕ} (hpos : 0 < R2_prime X n) :
    IsSumOfTwoPrimes n := by
  by_contra hnone
  have hzero : R2_prime X n = 0 := by
    unfold R2_prime
    apply Finset.sum_eq_zero; intro p₁ _
    apply Finset.sum_eq_zero; intro p₂ _
    split_ifs with h
    · exfalso; exact hnone ⟨p₁, p₂, h.1, h.2.1, h.2.2⟩
    · rfl
  linarith

/-- If Binary Goldbach holds up to `B`, then `E(X) = 0` for all `X ≤ B`. -/
theorem binaryExceptionalCount_eq_zero_of_le {B X : ℕ}
    (hB : BinaryGoldbachUpTo B) (hXB : X ≤ B) :
    binaryExceptionalCount X = 0 := by
  classical
  unfold binaryExceptionalCount binaryExceptionalSet
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n hn
  rw [Finset.mem_Icc] at hn
  intro ⟨heven, hnot⟩
  exact hnot (hB n hn.1 (le_trans hn.2 hXB) heven)

/-- Finset Chebyshev (`L²` Markov) inequality:
    if `∑_{n ∈ S} (f n)^2 ≤ U` and every `n ∈ E ⊆ S` has `c ≤ |f n|` (`c > 0`),
    then `|E| ≤ U / c^2`. -/
theorem card_le_of_sq_sum_le {S E : Finset ℕ} {f : ℕ → ℝ} {c U : ℝ}
    (hc : 0 < c) (hsub : E ⊆ S)
    (hge : ∀ n ∈ E, c ≤ |f n|)
    (hsum : ∑ n ∈ S, (f n) ^ 2 ≤ U) :
    (E.card : ℝ) ≤ U / c ^ 2 := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  rw [le_div_iff₀ hc2]
  calc (E.card : ℝ) * c ^ 2
      = ∑ _n ∈ E, c ^ 2 := by simp
    _ ≤ ∑ n ∈ E, (f n) ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        have h1 := hge n hn
        have hsq : c ^ 2 ≤ |f n| ^ 2 := pow_le_pow_left₀ (le_of_lt hc) h1 2
        simpa [sq_abs] using hsq
    _ ≤ ∑ n ∈ S, (f n) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    _ ≤ U := hsum

/-- Finset `L¹` Markov inequality:
    if `∑_{n ∈ S} |g n| ≤ V` and every `n ∈ E ⊆ S` has `c ≤ |g n|` (`c > 0`),
    then `|E| ≤ V / c`. -/
theorem card_le_of_abs_sum_le {S E : Finset ℕ} {g : ℕ → ℝ} {c V : ℝ}
    (hc : 0 < c) (hsub : E ⊆ S)
    (hge : ∀ n ∈ E, c ≤ |g n|)
    (hsum : ∑ n ∈ S, |g n| ≤ V) :
    (E.card : ℝ) ≤ V / c := by
  rw [le_div_iff₀ hc]
  calc (E.card : ℝ) * c
      = ∑ _n ∈ E, c := by simp
    _ ≤ ∑ n ∈ E, |g n| := Finset.sum_le_sum (fun n hn => hge n hn)
    _ ≤ ∑ n ∈ S, |g n| :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
    _ ≤ V := hsum

/-- Dyadic decomposition of `binaryExceptionalCount X`:
    `E(X) ≤ E(X / 2) + |dyadicExceptionalSet X|`. -/
theorem dyadic_split_card (X : ℕ) :
    binaryExceptionalCount X ≤
      binaryExceptionalCount (X / 2) + (dyadicExceptionalSet X).card := by
  classical
  unfold binaryExceptionalCount
  have hsub : binaryExceptionalSet X ⊆
      binaryExceptionalSet (X / 2) ∪ dyadicExceptionalSet X := by
    intro n hn
    unfold binaryExceptionalSet dyadicExceptionalSet at *
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hn ⊢
    rcases hn with ⟨⟨h4, hX⟩, heven, hnot⟩
    by_cases hle : n ≤ X / 2
    · left; exact ⟨⟨h4, hle⟩, heven, hnot⟩
    · right; exact ⟨⟨by omega, hX⟩, h4, heven, hnot⟩
  calc (binaryExceptionalSet X).card
      ≤ (binaryExceptionalSet (X / 2) ∪ dyadicExceptionalSet X).card :=
        Finset.card_le_card hsub
    _ ≤ (binaryExceptionalSet (X / 2)).card + (dyadicExceptionalSet X).card :=
        Finset.card_union_le _ _

/-- **Global Dyadic Summation Theorem (zero axioms):**
    If Binary Goldbach holds up to `B ≥ 4` and every dyadic slice `(Y / 2, Y]`
    for `Y > B` has at most `C₀ * √Y * (log Y)^k` exceptions, then for EVERY `X ≥ 4`,
    `E(X) ≤ (2 + √2) * C₀ * √X * (log X)^k`. -/
theorem global_bound_of_dyadic_sqrt_log {B : ℕ} (hB4 : 4 ≤ B)
    (hB : BinaryGoldbachUpTo B) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (k : ℕ)
    (hdyadic : ∀ Y : ℕ, B < Y →
      ((dyadicExceptionalSet Y).card : ℝ) ≤
        C₀ * Real.sqrt (Y : ℝ) * (Real.log (Y : ℝ)) ^ k) :
    ∀ X : ℕ, 4 ≤ X →
      (binaryExceptionalCount X : ℝ) ≤
        ((2 + Real.sqrt 2) * C₀) * Real.sqrt (X : ℝ) * (Real.log (X : ℝ)) ^ k := by
  intro X
  induction X using Nat.strong_induction_on with
  | h X ih =>
    intro hX4
    have hlogX_nonneg : 0 ≤ Real.log (X : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))
    by_cases hleB : X ≤ B
    · rw [binaryExceptionalCount_eq_zero_of_le hB hleB]
      simp only [Nat.cast_zero]
      positivity
    · have hgtB : B < X := by omega
      have hsplit : (binaryExceptionalCount X : ℝ) ≤
          (binaryExceptionalCount (X / 2) : ℝ) + ((dyadicExceptionalSet X).card : ℝ) := by
        exact_mod_cast dyadic_split_card X
      have hdy := hdyadic X hgtB
      -- Bound E(X / 2): if X / 2 < 4 then E(X / 2) = 0; otherwise apply IH.
      have hhalf_bound : (binaryExceptionalCount (X / 2) : ℝ) ≤
          ((2 + Real.sqrt 2) * C₀) * (Real.sqrt (X : ℝ) / Real.sqrt 2) *
            (Real.log (X : ℝ)) ^ k := by
        by_cases hsmall : X / 2 < 4
        · have hzero : binaryExceptionalCount (X / 2) = 0 := by
            classical
            unfold binaryExceptionalCount binaryExceptionalSet
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro n hn
            rw [Finset.mem_Icc] at hn
            omega
          rw [hzero]; simp only [Nat.cast_zero]; positivity
        · have hlt : X / 2 < X := Nat.div_lt_self (by omega) (by decide)
          have hih := ih (X / 2) hlt (by omega)
          have hhalf_le : ((X / 2 : ℕ) : ℝ) ≤ (X : ℝ) / 2 := by
            have h2 : 2 * (X / 2) ≤ X := Nat.mul_div_le X 2
            have h2' : (2 : ℝ) * ((X / 2 : ℕ) : ℝ) ≤ (X : ℝ) := by exact_mod_cast h2
            linarith
          have hsqrt_le : Real.sqrt ((X / 2 : ℕ) : ℝ) ≤ Real.sqrt (X : ℝ) / Real.sqrt 2 := by
            rw [← Real.sqrt_div (by positivity)]
            exact Real.sqrt_le_sqrt hhalf_le
          have hlog_le : (Real.log ((X / 2 : ℕ) : ℝ)) ^ k ≤ (Real.log (X : ℝ)) ^ k := by
            have hpos_half : (0 : ℝ) < ((X / 2 : ℕ) : ℝ) := by
              exact_mod_cast (by omega : 0 < X / 2)
            have hlog_nonneg_h : 0 ≤ Real.log ((X / 2 : ℕ) : ℝ) :=
              Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X / 2))
            have hlog_mono : Real.log ((X / 2 : ℕ) : ℝ) ≤ Real.log (X : ℝ) :=
              Real.log_le_log hpos_half (by exact_mod_cast (Nat.div_le_self X 2))
            exact pow_le_pow_left₀ hlog_nonneg_h hlog_mono k
          have hc_nonneg : 0 ≤ (2 + Real.sqrt 2) * C₀ := by positivity
          calc (binaryExceptionalCount (X / 2) : ℝ)
              ≤ ((2 + Real.sqrt 2) * C₀) * Real.sqrt ((X / 2 : ℕ) : ℝ) *
                  (Real.log ((X / 2 : ℕ) : ℝ)) ^ k := hih
            _ ≤ ((2 + Real.sqrt 2) * C₀) * (Real.sqrt (X : ℝ) / Real.sqrt 2) *
                  (Real.log (X : ℝ)) ^ k := by
                apply mul_le_mul
                · exact mul_le_mul_of_nonneg_left hsqrt_le hc_nonneg
                · exact hlog_le
                · positivity
                · positivity
      -- Combine: (2 + √2)/√2 + 1 = 2 + √2
      have hgeom : (2 + Real.sqrt 2) / Real.sqrt 2 + 1 = 2 + Real.sqrt 2 := by
        have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
        have hne : Real.sqrt 2 ≠ 0 := by positivity
        field_simp
        nlinarith
      calc (binaryExceptionalCount X : ℝ)
          ≤ (binaryExceptionalCount (X / 2) : ℝ) + ((dyadicExceptionalSet X).card : ℝ) := hsplit
        _ ≤ ((2 + Real.sqrt 2) * C₀) * (Real.sqrt (X : ℝ) / Real.sqrt 2) * (Real.log (X : ℝ)) ^ k +
              C₀ * Real.sqrt (X : ℝ) * (Real.log (X : ℝ)) ^ k := add_le_add hhalf_bound hdy
        _ = ((2 + Real.sqrt 2) / Real.sqrt 2 + 1) * C₀ * Real.sqrt (X : ℝ) * (Real.log (X : ℝ)) ^ k := by
              ring
        _ = ((2 + Real.sqrt 2) * C₀) * Real.sqrt (X : ℝ) * (Real.log (X : ℝ)) ^ k := by
              rw [hgeom]

/-- **Asymptotic Density-1 Theorem (zero axioms):**
    Any bound `E(X) ≤ C * √X * (log X)^k` for `X ≥ 4` implies `E(X) / X → 0` as `X → ∞`
    (almost all even integers are sums of two primes). -/
theorem density_one_of_sqrt_log_bound {C : ℝ} (k : ℕ)
    (hbound : ∀ X : ℕ, 4 ≤ X →
      (binaryExceptionalCount X : ℝ) ≤ C * Real.sqrt (X : ℝ) * (Real.log (X : ℝ)) ^ k) :
    Filter.Tendsto (fun X : ℕ => (binaryExceptionalCount X : ℝ) / (X : ℝ))
      Filter.atTop (nhds 0) := by
  -- Use `isLittleO_log_rpow_atTop`: (log x)^k / x^(1/2) → 0 as x → ∞
  have hreal : Filter.Tendsto (fun x : ℝ => C * ((Real.log x) ^ k / x ^ ((1 : ℝ) / 2)))
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun x : ℝ => (Real.log x) ^ k / x ^ ((1 : ℝ) / 2))
        Filter.atTop (nhds 0) := by
      have hlt := isLittleO_log_rpow_rpow_atTop (k : ℝ) (show (0 : ℝ) < (1 : ℝ) / 2 by norm_num)
      have htend := hlt.tendsto_div_nhds_zero
      refine htend.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
      rw [Real.rpow_natCast]
    simpa using h0.const_mul C
  have hnat : Filter.Tendsto
      (fun X : ℕ => C * ((Real.log (X : ℝ)) ^ k / (X : ℝ) ^ ((1 : ℝ) / 2)))
      Filter.atTop (nhds 0) :=
    hreal.comp tendsto_natCast_atTop_atTop
  refine squeeze_zero' ?_ ?_ hnat
  · filter_upwards with X
    positivity
  · filter_upwards [Filter.eventually_ge_atTop 4] with X hX
    have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
    have hle := hbound X hX
    have hdiv : (binaryExceptionalCount X : ℝ) / (X : ℝ) ≤
        (C * Real.sqrt (X : ℝ) * (Real.log (X : ℝ)) ^ k) / (X : ℝ) :=
      div_le_div_of_nonneg_right hle (le_of_lt hXpos)
    have hsimp : (C * Real.sqrt (X : ℝ) * (Real.log (X : ℝ)) ^ k) / (X : ℝ) =
        C * ((Real.log (X : ℝ)) ^ k / (X : ℝ) ^ ((1 : ℝ) / 2)) := by
      rw [Real.sqrt_eq_rpow]
      have hXeq : (X : ℝ) ^ ((1 : ℝ) / 2) * (X : ℝ) ^ ((1 : ℝ) / 2) = (X : ℝ) := by
        rw [← Real.rpow_add hXpos]; norm_num
      have hne1 : (X : ℝ) ≠ 0 := ne_of_gt hXpos
      have hne2 : (X : ℝ) ^ ((1 : ℝ) / 2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hXpos _)
      field_simp
      calc C * (X : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (X : ℝ)) ^ k * (X : ℝ) ^ ((1 : ℝ) / 2)
          = C * (Real.log (X : ℝ)) ^ k * ((X : ℝ) ^ ((1 : ℝ) / 2) * (X : ℝ) ^ ((1 : ℝ) / 2)) := by ring
        _ = C * (Real.log (X : ℝ)) ^ k * (X : ℝ) := by rw [hXeq]
    linarith

end WeakGoldbach

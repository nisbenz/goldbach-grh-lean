import Mathlib

-- B-017: exact Liouville prime detector on cube-root-rough integers.
-- Eq.(5) of goldbach-grh-lean/proof/strong_goldbach_erh_attack.md, formalized.
namespace GoldbachAttack

open ArithmeticFunction

-- A list of naturals each > z has product >= z^length.
lemma list_prod_ge_pow_of_forall_gt (l : List ℕ) (z : ℕ) (h : ∀ p ∈ l, z < p) :
    z ^ l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : z < a := h a (by simp)
      have hl : ∀ p ∈ l, z < p := fun p hp => h p (by simp [hp])
      have ih' := ih hl
      simp only [List.length_cons, List.prod_cons, pow_succ]
      have hle_a : z ≤ a := Nat.le_of_lt ha
      have hmul : z ^ l.length * z ≤ l.prod * a := Nat.mul_le_mul ih' hle_a
      simpa [mul_comm] using hmul

-- If m < z^3 and every prime factor of m exceeds z, then m has at most 2 prime factors
-- (counted with multiplicity): three factors > z would multiply to more than z^3.
lemma primeFactorsList_length_le_two (z m : ℕ) (hm0 : m ≠ 0) (hmz : m < z ^ 3)
    (hrough : ∀ p, Nat.Prime p → p ∣ m → z < p) :
    m.primeFactorsList.length ≤ 2 := by
  have hzpos : 0 < z := by
    by_contra hz
    have hz0 : z = 0 := by omega
    subst z
    simp at hmz
  have hall : ∀ p ∈ m.primeFactorsList, z < p := by
    intro p hp
    exact hrough p (Nat.prime_of_mem_primeFactorsList hp) (Nat.dvd_of_mem_primeFactorsList hp)
  have hprod := list_prod_ge_pow_of_forall_gt m.primeFactorsList z hall
  rw [Nat.prod_primeFactorsList hm0] at hprod
  by_contra hnot
  have hlen : 3 ≤ m.primeFactorsList.length := by omega
  have hpow : z ^ 3 ≤ z ^ m.primeFactorsList.length := by
    exact Nat.pow_le_pow_right hzpos hlen
  omega

-- B-017 main theorem: exact prime detector on cube-root-rough integers.
theorem liouville_prime_detector_cuberough
    (z m : ℕ) (hz : 0 < z) (hm1 : 1 < m) (hmz : m < z ^ 3)
    (hrough : ∀ p, Nat.Prime p → p ∣ m → z < p) :
    (1 - liouville m) / 2 = if Nat.Prime m then (1 : ℤ) else 0 := by
  have hm0 : m ≠ 0 := by omega
  have hlen : cardFactors m ≤ 2 := by
    rw [cardFactors_apply]
    exact primeFactorsList_length_le_two z m hm0 hmz hrough
  have hpos : 0 < cardFactors m := cardFactors_pos_iff_one_lt.mpr hm1
  have hcases : cardFactors m = 1 ∨ cardFactors m = 2 := by omega
  by_cases hprime : Nat.Prime m
  · simp [hprime]
    have hcf1 : cardFactors m = 1 := cardFactors_eq_one_iff_prime.mpr hprime
    have hl : liouville m = -1 := by
      rw [liouville_apply hm0, hcf1]
      norm_num
    rw [hl]
    norm_num
  · simp [hprime]
    have hcf1false : cardFactors m ≠ 1 := by
      intro h1
      exact hprime (cardFactors_eq_one_iff_prime.mp h1)
    have hcf2 : cardFactors m = 2 := by omega
    have hl : liouville m = 1 := by
      rw [liouville_apply hm0, hcf2]
      norm_num
    rw [hl]
    norm_num

end GoldbachAttack

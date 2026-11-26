import Mathlib
import Goldbach.Basic

-- The combinatorial core of the H1 criterion, formalized without analysis.
namespace GoldbachAttack

-- Ordered count of representations n = p + q with both p and q prime.
def primePairCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).card

-- If the prime-pair count is positive, Goldbach holds for that n.
theorem goldbach_of_primePairCount_pos {n : ℕ} (h : 0 < primePairCount n) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  unfold primePairCount at h
  have hne : ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).Nonempty :=
    Finset.card_pos.mp h
  obtain ⟨p, hp_mem⟩ := hne
  have hp_range : p ∈ Finset.range (n + 1) := (Finset.mem_filter.mp hp_mem).1
  have hpq : Nat.Prime p ∧ Nat.Prime (n - p) := (Finset.mem_filter.mp hp_mem).2
  have hp_prime : Nat.Prime p := hpq.1
  have hq_prime : Nat.Prime (n - p) := hpq.2
  refine ⟨p, n - p, hp_prime, hq_prime, ?_⟩
  have hp_le : p ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hp_range)
  omega

-- Finite-verification consequence: positive count for every even n in a range implies UpTo.
theorem binaryGoldbachUpTo_of_count_pos (B : ℕ)
    (h : ∀ n : ℕ, 2 < n → n ≤ B → Even n → 0 < primePairCount n) :
    BinaryGoldbachUpTo B := by
  intro n hn2 hnB hneven
  exact goldbach_of_primePairCount_pos (h n hn2 hnB hneven)

end GoldbachAttack

import Mathlib

-- Pure inequality lemmas from the exceptional-set dyadic summation, formalized without axioms.
-- This is the rational-ratio counterpart of the repo's Lemma 7 geometric bound.
namespace GoldbachAttack

-- Finite geometric sum with ratio 1/2 is < 2 (a clean, kernel-checkable version of the
-- dyadic-summation step). Proved by the closed-form sum of a geometric progression.
lemma geom_sum_half_lt_two (m : ℕ) :
    (∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ j) < 2 := by
  have hsum : (∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ j) = 2 - 2 * (1 / 2 : ℝ) ^ m := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  rw [hsum]
  have hpos : 0 < (2 : ℝ) * (1 / 2 : ℝ) ^ m := by positivity
  linarith

-- The dyadic count bound shape: a geometric sum with ratio <= 1/2 is bounded by twice its first
-- term. Used to turn a per-dyadic-block count into a global count.
lemma dyadic_global_bound (a : ℕ → ℝ) (m : ℕ)
    (h : ∀ j < m, a j ≤ 410000 * (1 / 2 : ℝ) ^ j) :
    (∑ j ∈ Finset.range m, a j) ≤ 820000 := by
  calc
    (∑ j ∈ Finset.range m, a j)
        ≤ ∑ j ∈ Finset.range m, 410000 * (1 / 2 : ℝ) ^ j := by
            exact Finset.sum_le_sum (fun j hj => h j (Finset.mem_range.mp hj))
    _ = 410000 * (∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ j) := by
        rw [Finset.mul_sum]
    _ ≤ 410000 * 2 := by
        have hlt := geom_sum_half_lt_two m
        nlinarith
    _ = 820000 := by norm_num

end GoldbachAttack

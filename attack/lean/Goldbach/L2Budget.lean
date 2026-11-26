import Mathlib

-- B-010 proposed micro-step: a nonnegative mean-square budget bounds every individual
-- coefficient. Pure finset/order; the logical kernel of the L^2 -> sup deduction.
namespace GoldbachAttack

lemma sq_coeff_le_sum_of_l2_budget
    {ι : Type*} [Fintype ι] (E : ι → ℝ) (B : ℝ)
    (hbudget : ∑ i, (E i) ^ 2 ≤ B) (i0 : ι) :
    (E i0) ^ 2 ≤ B := by
  exact (Finset.single_le_sum (fun j _ => sq_nonneg (E j)) (Finset.mem_univ i0)).trans hbudget

-- Companion: a mean-square budget bounds the average coefficient (card * min <= sum).
lemma card_mul_min_sq_le_sum
    {ι : Type*} [Fintype ι] [Nonempty ι] (E : ι → ℝ) (B : ℝ)
    (hbudget : ∑ i, (E i) ^ 2 ≤ B) :
    Fintype.card ι * (⨅ i, (E i) ^ 2) ≤ B := by
  have hbdd : BddBelow (Set.range (fun i => (E i) ^ 2)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact sq_nonneg (E i)
  have hle_each : ∀ j : ι, (⨅ i, (E i) ^ 2) ≤ (E j) ^ 2 := by
    intro j
    exact ciInf_le hbdd j
  calc
    Fintype.card ι * (⨅ i, (E i) ^ 2)
        = ∑ _ : ι, (⨅ i, (E i) ^ 2) := by simp
    _ ≤ ∑ i, (E i) ^ 2 := Finset.sum_le_sum (fun j _ => hle_each j)
    _ ≤ B := hbudget

end GoldbachAttack

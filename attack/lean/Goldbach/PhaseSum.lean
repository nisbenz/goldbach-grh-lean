import Mathlib

-- B-011 proposed micro-step: finite geometric-sum phase-cancellation bound.
-- For a complex w with |w| <= 1 and w != 1, |sum_{j<M} w^j| <= 2 / |1 - w|.
-- This is the finite form used to bound same-sign zero-pair phases in the pair kernel
-- (there w is a unit, so |w| = 1).
namespace GoldbachAttack

lemma geom_sum_phase_bound (w : ℂ) (M : ℕ) (hw_unit : ‖w‖ ≤ 1) (hw : w ≠ 1) :
    ‖∑ j ∈ Finset.range M, w ^ j‖ ≤ 2 / ‖1 - w‖ := by
  have hden : ‖1 - w‖ ≠ 0 := by
    intro h
    apply hw
    have hz : (1 : ℂ) - w = 0 := norm_eq_zero.mp h
    exact eq_comm.mp (sub_eq_zero.mp hz)
  have hsum : (∑ j ∈ Finset.range M, w ^ j) * (1 - w) = 1 - w ^ M := by
    induction M with
    | zero => simp
    | succ M ih =>
        rw [Finset.sum_range_succ, add_mul, ih]
        ring
  have hnorm : ‖∑ j ∈ Finset.range M, w ^ j‖ * ‖1 - w‖ = ‖1 - w ^ M‖ := by
    rw [← norm_mul, hsum]
  have hunitM : ‖1 - w ^ M‖ ≤ 2 := by
    have hwM : ‖w ^ M‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg w) hw_unit
    calc
      ‖1 - w ^ M‖ ≤ ‖(1 : ℂ)‖ + ‖w ^ M‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by rw [norm_one]; linarith
      _ = 2 := by norm_num
  have hmul : ‖∑ j ∈ Finset.range M, w ^ j‖ * ‖1 - w‖ ≤ 2 := by
    simpa [hnorm] using hunitM
  have hpos : 0 < ‖1 - w‖ := norm_pos_iff.mpr (by simpa using hden)
  rw [le_div_iff₀ hpos]
  simpa [mul_comm] using hmul

end GoldbachAttack

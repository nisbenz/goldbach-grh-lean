import Mathlib

-- B-013: reflection-hole witness. In Z/32Z, a set D with no two elements summing to 0 mod 32,
-- so (1_D * 1_D)(0) = 0. Found by src/find_reflection_hole.py (seed 1).
-- The Fourier-smallness part of the doc's claim is probabilistic and NOT formalized here.
namespace GoldbachAttack

def hole32 : Finset ℕ := {1, 2, 4, 9, 10, 12, 15, 18, 19, 21, 24, 25, 26, 27, 29}

-- No pair a,b in hole32 has (a+b) mod 32 = 0. Closed decidable proposition, kernel-checked.
lemma hole32_no_pair_sum_zero :
    ∀ a ∈ hole32, ∀ b ∈ hole32, (a + b) % 32 ≠ 0 := by
  decide

end GoldbachAttack

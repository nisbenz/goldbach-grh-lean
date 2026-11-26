import Mathlib

-- The two Goldbach conjectures, stated exactly. Nothing is proved here.
namespace GoldbachAttack

-- Binary (strong) Goldbach: every even n > 2 is the sum of two primes.
def BinaryGoldbach : Prop :=
  ∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

-- Weak (ternary) Goldbach: every odd n > 5 is the sum of three primes.
def WeakGoldbach : Prop :=
  ∀ n : ℕ, 5 < n → Odd n → ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

-- Binary Goldbach up to a bound.
def BinaryGoldbachUpTo (B : ℕ) : Prop :=
  ∀ n : ℕ, 2 < n → n ≤ B → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

-- Weak Goldbach from a bound N0 onward (the conditional finite-ladder shape).
def WeakGoldbachFrom (N0 : ℕ) : Prop :=
  ∀ n : ℕ, N0 ≤ n → Odd n → ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

end GoldbachAttack

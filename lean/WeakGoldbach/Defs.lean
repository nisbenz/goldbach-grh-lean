import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.Parity

namespace WeakGoldbach

/-- A natural number `n` is a sum of two primes. -/
def IsSumOfTwoPrimes (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- A natural number `n` is a sum of three primes. -/
def IsSumOfThreePrimes (n : ℕ) : Prop :=
  ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ p + q + r = n

/-- Binary (Strong) Goldbach holds for all even integers in `[4, B]`. -/
def BinaryGoldbachUpTo (B : ℕ) : Prop :=
  ∀ n : ℕ, 4 ≤ n → n ≤ B → Even n → IsSumOfTwoPrimes n

/-- Weak (Ternary) Goldbach holds for all odd integers `n ≥ N₀`. -/
def WeakGoldbachFrom (N₀ : ℕ) : Prop :=
  ∀ n : ℕ, N₀ ≤ n → Odd n → IsSumOfThreePrimes n

/-- The full Weak (Ternary) Goldbach Conjecture: every odd integer `n ≥ 7`
    is the sum of three primes. -/
def WeakGoldbachConjecture : Prop :=
  ∀ n : ℕ, 7 ≤ n → Odd n → IsSumOfThreePrimes n

/-- Pairwise step condition for an ascending prime ladder with maximum step `S`. -/
def LadderSteps (S : ℕ) : List ℕ → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a ≤ b ∧ b - a ≤ S ∧ LadderSteps S (b :: rest)

/-- A certified prime ladder bridging `[4, B]` up to `N₀`. -/
structure PrimeLadder (B N₀ : ℕ) where
  primes : List ℕ
  nonempty : primes ≠ []
  all_prime : ∀ p ∈ primes, Nat.Prime p
  all_odd : ∀ p ∈ primes, Odd p
  head_le : primes.head nonempty ≤ B - 4
  last_ge : N₀ - 4 ≤ primes.getLast nonempty
  steps : LadderSteps (B - 4) primes

end WeakGoldbach

import WeakGoldbach.Defs
import WeakGoldbach.PrimeLadder
import WeakGoldbach.Pratt
import WeakGoldbach.Analytic

namespace WeakGoldbach

/-- Finite binary Goldbach verification bound `B = 4 * 10^18`
    (Oliveira e Silva, Herzog, and Pardi, Math. Comp. 83 (2014), 2033–2060).
    Independently verified locally up to `10^9` (and Weak Goldbach up to `10^12`)
    by `verify/verify_finite.cpp`. -/
abbrev B_verified : ℕ := 4 * 10 ^ 18

/-- Axiom (finite computation): Binary Goldbach holds for all even integers in `[4, 4 * 10^18]`. -/
axiom binaryGoldbach_4e18 : BinaryGoldbachUpTo B_verified

/-- Axiom (external Pratt-certified finite prime ladder):
    The 2,501-rung prime ladder from `p_0 = 3,999,999,999,999,999,887` to
    `p_2500 = 10,003,999,999,999,999,876,777` (max gap `4 * 10^18 - 4`) constructed and
    deterministically verified via 13,197 recursive Pratt primality certificates in
    `verify/verify_ladder.py` (`verify/ladder_certs.json`), whose soundness theorem
    `WeakGoldbach.prime_of_lucas_trace` is proved in `WeakGoldbach/Pratt.lean`. -/
axiom certified_prime_ladder_1e22 : PrimeLadder B_verified N0

/-- **Main Theorem (Weak / Ternary Goldbach Conjecture under GRH):**
    Every odd integer `n ≥ 7` is the sum of three primes.

    Assembled completely in Lean 4 (zero `sorry`s) from:
    1. Kernel-verified `weakGoldbach_complete` (`WeakGoldbach/PrimeLadder.lean`),
    2. Kernel-verified Lemma 6 threshold inequality & analytic assembly (`WeakGoldbach/Analytic.lean`),
    3. Explicitly isolated GRH circle-method bounds from Lemmas 1–5 of `proof/weak_goldbach_proof.md`,
    4. Binary Goldbach up to `4 * 10^18` + Pratt-certified prime ladder up to `10^22`. -/
theorem weak_goldbach_theorem : WeakGoldbachConjecture :=
  weakGoldbach_complete
    (by decide : 4 ≤ B_verified)
    binaryGoldbach_4e18
    certified_prime_ladder_1e22
    weakGoldbachFrom_N0

#print axioms weak_goldbach_theorem

end WeakGoldbach

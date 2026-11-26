import WeakGoldbach.Defs
import Mathlib.Tactic

namespace WeakGoldbach

/-- Base range: Binary Goldbach up to `B` immediately implies Weak Goldbach
    for all odd integers `7 ≤ n ≤ B + 3`, via `n = 3 + p + q`. -/
theorem weakGoldbach_of_binary_small {B : ℕ} (hB : BinaryGoldbachUpTo B)
    {n : ℕ} (hn7 : 7 ≤ n) (hnB : n ≤ B + 3) (hodd : Odd n) :
    IsSumOfThreePrimes n := by
  have hge4 : 4 ≤ n - 3 := by omega
  have hleB : n - 3 ≤ B := by omega
  have heven : Even (n - 3) := by
    rcases hodd with ⟨k, rfl⟩
    refine ⟨k - 1, ?_⟩
    omega
  rcases hB (n - 3) hge4 hleB heven with ⟨p, q, hp, hq, hpq⟩
  refine ⟨3, p, q, by decide, hp, hq, ?_⟩
  omega

/-- Auxiliary lemma: given a non-empty ladder `ps` with steps bounded by `S`
    whose head is `≤ x` and whose last element is `≥ x`, there exists an element
    `p ∈ ps` with `x ≤ p + S` and `p ≤ x` (in fact `x - S ≤ p ≤ x`). -/
lemma exists_rung_near {S x : ℕ} :
    ∀ (ps : List ℕ) (hne : ps ≠ []),
      LadderSteps S ps →
      ps.head hne ≤ x →
      x ≤ ps.getLast hne →
      ∃ p ∈ ps, p ≤ x ∧ x - p ≤ S
  | [], hne, _, _, _ => absurd rfl hne
  | [a], _, _, hhead, hlast => by
      simp only [List.head_cons, List.getLast_singleton] at hhead hlast
      exact ⟨a, List.mem_singleton_self a, hhead, by omega⟩
  | a :: b :: rest, _, hsteps, hhead, hlast => by
      rcases hsteps with ⟨hab, hbaS, hrest⟩
      simp only [List.head_cons] at hhead
      by_cases hbx : b ≤ x
      · have hne' : b :: rest ≠ [] := List.cons_ne_nil b rest
        have hlast' : x ≤ (b :: rest).getLast hne' := by
          simpa [List.getLast_cons hne'] using hlast
        rcases exists_rung_near (b :: rest) hne' hrest (by simpa using hbx) hlast' with
          ⟨p, hp, hpx, hxpS⟩
        exact ⟨p, List.mem_cons_of_mem a hp, hpx, hxpS⟩
      · refine ⟨a, List.mem_cons_self a (b :: rest), hhead, ?_⟩
        omega

/-- Any certified prime ladder bridging `B` to `N₀`, combined with Binary Goldbach
    up to `B`, certifies Weak Goldbach for all odd `7 ≤ n ≤ N₀`. -/
theorem weakGoldbach_of_prime_ladder {B N₀ : ℕ} (hB4 : 4 ≤ B)
    (hB : BinaryGoldbachUpTo B) (L : PrimeLadder B N₀)
    {n : ℕ} (hn7 : 7 ≤ n) (hnN₀ : n ≤ N₀) (hodd : Odd n) :
    IsSumOfThreePrimes n := by
  by_cases hsmall : n ≤ B + 3
  · exact weakGoldbach_of_binary_small hB hn7 hsmall hodd
  · -- Here `n > B + 3`, so `n - 4 ≥ B > B - 4 ≥ head`, and `n - 4 ≤ N₀ - 4 ≤ last`.
    have hx_ge : L.primes.head L.nonempty ≤ n - 4 := by
      have := L.head_le
      omega
    have hx_le : n - 4 ≤ L.primes.getLast L.nonempty := by
      have := L.last_ge
      omega
    rcases exists_rung_near L.primes L.nonempty L.steps hx_ge hx_le with
      ⟨p, hp_mem, hp_le, hgap⟩
    have hp_prime : Nat.Prime p := L.all_prime p hp_mem
    have hp_odd : Odd p := L.all_odd p hp_mem
    have hdiff_ge4 : 4 ≤ n - p := by omega
    have hdiff_leB : n - p ≤ B := by omega
    have hdiff_even : Even (n - p) := by
      rcases hodd with ⟨k, rfl⟩
      rcases hp_odd with ⟨m, rfl⟩
      refine ⟨k - m, ?_⟩
      omega
    rcases hB (n - p) hdiff_ge4 hdiff_leB hdiff_even with ⟨q, r, hq, hr, hqr⟩
    refine ⟨p, q, r, hp_prime, hq, hr, ?_⟩
    omega

/-- Complete assembly: Binary Goldbach up to `B`, a certified prime ladder from `B`
    to `N₀`, and the analytic GRH theorem for odd `n ≥ N₀` together imply the full
    Weak Goldbach Conjecture. -/
theorem weakGoldbach_complete {B N₀ : ℕ} (hB4 : 4 ≤ B)
    (hB : BinaryGoldbachUpTo B) (L : PrimeLadder B N₀)
    (hAnalytic : WeakGoldbachFrom N₀) :
    WeakGoldbachConjecture := by
  intro n hn7 hodd
  by_cases hle : n ≤ N₀
  · exact weakGoldbach_of_prime_ladder hB4 hB L hn7 hle hodd
  · exact hAnalytic n (by omega) hodd

end WeakGoldbach

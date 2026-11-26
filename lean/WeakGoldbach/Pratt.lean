import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic

namespace WeakGoldbach

/-- Flat, thunk-free modular exponentiation trace checker.
    Verifies `(acc * base ^ exp) % mod = target` by checking each bit step
    against literal intermediate values `(nextAcc, nextBase)`.
    Because every step multiplies literal `Nat`s, Lean's kernel checks it in
    strict `O(log exp)` GMP operations via `rfl` with zero thunk blowup. -/
def checkPowTrace (mod : ℕ) : ℕ → ℕ → ℕ → List (ℕ × ℕ) → ℕ → Bool
  | acc, _, exp, [], target => (exp == 0) && (acc % mod == target)
  | acc, base, exp, (nextAcc, nextBase) :: rest, target =>
      (exp != 0) &&
      (nextAcc == if exp % 2 == 1 then (acc * base) % mod else acc) &&
      (nextBase == (base * base) % mod) &&
      checkPowTrace mod nextAcc nextBase (exp / 2) rest target

theorem checkPowTrace_sound (mod : ℕ) :
    ∀ (trace : List (ℕ × ℕ)) (acc base exp target : ℕ),
      checkPowTrace mod acc base exp trace target = true →
      (acc * base ^ exp) % mod = target
  | [], acc, base, exp, target, h => by
      simp only [checkPowTrace, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨rfl, hacc⟩
      simpa using hacc
  | (nextAcc, nextBase) :: rest, acc, base, exp, target, h => by
      simp only [checkPowTrace, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at h
      rcases h with ⟨⟨⟨hexp0, hna⟩, hnb⟩, hrest⟩
      have ih := checkPowTrace_sound mod rest nextAcc nextBase (exp / 2) target hrest
      rw [← ih, hna, hnb]
      by_cases hodd : exp % 2 = 1
      · simp only [hodd, ↓reduceIte]
        have he : exp = 1 + 2 * (exp / 2) := by omega
        conv_lhs => rw [he, pow_add, pow_one, pow_mul, sq]
        rw [← mul_assoc]
        simp [Nat.mul_mod, Nat.pow_mod]
      · simp only [hodd, ↓reduceIte]
        have he : exp = 2 * (exp / 2) := by omega
        conv_lhs => rw [he, pow_mul, sq]
        simp [Nat.mul_mod, Nat.pow_mod]

/-- Check `g ^ e % p = target` via a flat squaring trace. -/
def checkPow (p g e : ℕ) (trace : List (ℕ × ℕ)) (target : ℕ) : Bool :=
  checkPowTrace p 1 (g % p) e trace target

theorem checkPow_sound {p g e target : ℕ} {trace : List (ℕ × ℕ)}
    (h : checkPow p g e trace target = true) :
    g ^ e % p = target := by
  have h1 := checkPowTrace_sound p trace 1 (g % p) e target h
  simpa [Nat.pow_mod] using h1

/-- Every prime dividing `∏ (q_i ^ e_i)` equals some `q_i`, assuming all `q_i` are prime. -/
lemma prime_dvd_factorList {r : ℕ} (hr : Nat.Prime r) :
    ∀ (factors : List (ℕ × ℕ)),
      (∀ x ∈ factors, Nat.Prime x.1) →
      r ∣ (factors.map (fun x => x.1 ^ x.2)).prod →
      ∃ x ∈ factors, x.1 = r
  | [], _, hdvd => by
      simp at hdvd
      exact absurd hdvd (Nat.Prime.ne_one hr)
  | (q, e) :: rest, hprimes, hdvd => by
      simp only [List.map_cons, List.prod_cons] at hdvd
      rcases hr.dvd_mul.mp hdvd with h1 | h2
      · have hrq : r ∣ q := hr.dvd_of_dvd_pow h1
        have hq : Nat.Prime q := hprimes (q, e) (List.mem_cons_self _ _)
        rcases (Nat.dvd_prime hq).mp hrq with h_eq | h_eq
        · exact absurd h_eq hr.ne_one
        · exact ⟨(q, e), List.mem_cons_self _ _, h_eq.symm⟩
      · rcases prime_dvd_factorList hr rest
            (fun x hx => hprimes x (List.mem_cons_of_mem _ hx)) h2 with ⟨x, hx, hxq⟩
        exact ⟨x, List.mem_cons_of_mem _ hx, hxq⟩

/-- A single Lucas/Pratt certificate step for `p > 2`, given proofs that each
    prime factor `q` of `p - 1` is prime, plus flat squaring traces for
    `g^(p-1) % p = 1` and `g^((p-1)/q) % p = r_q ≠ 1`. -/
theorem prime_of_lucas_trace (p g : ℕ) (hp : 2 < p)
    (fermatTrace : List (ℕ × ℕ))
    (hfermat : checkPow p g (p - 1) fermatTrace 1 = true)
    (factors : List (ℕ × ℕ × ℕ × List (ℕ × ℕ)))
    (hprod : (factors.map (fun f => f.1 ^ f.2.1)).prod = p - 1)
    (hfac_prime : ∀ f ∈ factors, Nat.Prime f.1)
    (hfac_order : ∀ f ∈ factors,
      f.2.2.1 ≠ 1 ∧ checkPow p g ((p - 1) / f.1) f.2.2.2 f.2.2.1 = true) :
    Nat.Prime p := by
  haveI : NeZero p := ⟨by omega⟩
  apply lucas_primality p (g : ZMod p)
  · have hmod := checkPow_sound hfermat
    have h1 : ((g ^ (p - 1) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [← ZMod.natCast_mod, hmod]
    simpa using h1
  · intro q hq hqdvd
    have hsub : ∀ x ∈ factors.map (fun f => (f.1, f.2.1)), Nat.Prime x.1 := by
      intro x hx
      rcases List.mem_map.mp hx with ⟨f, hf, rfl⟩
      exact hfac_prime f hf
    have hmap : ((factors.map (fun f => (f.1, f.2.1))).map (fun x => x.1 ^ x.2)).prod = p - 1 := by
      simpa [List.map_map, Function.comp] using hprod
    rw [← hmap] at hqdvd
    rcases prime_dvd_factorList hq _ hsub hqdvd with ⟨x, hx, hxq⟩
    rcases List.mem_map.mp hx with ⟨f, hf, rfl⟩
    subst hxq
    intro heq
    have hmod_eq : g ^ ((p - 1) / f.1) % p = 1 % p := by
      have hcast : ((g ^ ((p - 1) / f.1) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
        simpa using heq
      exact (ZMod.natCast_eq_natCast_iff' _ _ p).mp hcast
    rw [Nat.mod_eq_of_lt (by omega : 1 < p)] at hmod_eq
    have hord := hfac_order f hf
    have hrem := checkPow_sound hord.2
    exact hord.1 (by omega)

end WeakGoldbach

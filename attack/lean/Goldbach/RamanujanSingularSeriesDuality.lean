import Mathlib

/-!
# Wave 33: Klüyver's Ramanujan Sum Identity, Exact Ramanujan Orthogonality & Parseval Energy, Ramanujan = Goldbach Singular Series & Purely Real Finite Ramanujan Expansion of `∑_{d ∈ S, d ∣ x} μ(d)`

In Wave 32 (`FareyMoebiusDuality.lean`), we proved the exact complex Farey–Möbius duality identity
localizing 100% of the Pure Square `[1/2, 1]^2` to the top primitive Farey shell `q ∈ (D₁/(log n)^C, 2 D₁]`.

Wave 33 eliminates ALL complex exponentials by proving from scratch in Lean 4
(standard axioms `[propext, Classical.choice, Quot.sound]` only) that the primitive Farey kernel
is identically **Ramanujan's integer sum `c_q(m)`**, connecting Wave 24's Goldbach singular series
and Wave 32's Farey–Möbius localization into one unified Ramanujan harmonic framework:

## Main Theorems in this File
1. **`ramanujanSum_eq_complex_exp_sum` (Klüyver's Identity)**:
   Defining the pure integer sum `ramanujanSum q m := ∑ h ∈ (Nat.gcd q m).divisors, (h : ℤ) * μ (q / h)`,
   proves for every `0 < q` and `m : ℕ`:
   `∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), exp(2πi a m / q) = (ramanujanSum q m : ℂ)`.
2. **`ramanujanSum_prime` & `ramanujan_local_euler_eq_goldbach_singular_series`**:
   Proves `ramanujanSum p m = if p ∣ m then p - 1 else -1` for every prime `p`, and proves the
   exact prime-by-prime Ramanujan–Hardy–Littlewood identity:
   `1 + (ramanujanSum p n : ℝ) / (p - 1)² = localSingularFactor n p` for every even `n` and prime `p`!
3. **`ramanujan_sum_orthogonality`**:
   For ANY `0 < Q` and ANY `q₁, q₂ ∣ Q`:
   `∑ m ∈ Finset.range Q, ramanujanSum q₁ m * ramanujanSum q₂ m = if q₁ = q₂ then (Q * Nat.totient q₁ : ℤ) else 0`!
4. **`divisor_moebius_ramanujan_expansion_exact`**:
   Purely real (zero complex numbers!) exact finite Ramanujan expansion of ANY truncated Möbius
   divisor sum (`S ⊆ Icc 1 D_max`, `x : ℕ`):
   `∑ d ∈ S.filter (· ∣ x), (μ d : ℝ)`
   `= ∑ q ∈ Icc 1 D_max, ((μ q : ℝ) / q) * (∑ m ∈ (Icc 1 (D_max / q)).filter (fun m => q * m ∈ S ∧ Coprime m q), (μ m : ℝ) / m) * (ramanujanSum q x : ℝ)`!
5. **`ramanujan_parseval_energy`**:
   Exact Parseval energy identity for ANY Ramanujan expansion `F(m) = ∑_{q ∣ Q} α_q * c_q(m)` on `ℤ / Qℤ`:
   `∑ m ∈ Finset.range Q, (∑ q ∈ Q.divisors, α q * (ramanujanSum q m : ℝ)) ^ 2 = (Q : ℝ) * ∑ q ∈ Q.divisors, (Nat.totient q : ℝ) * (α q) ^ 2`!
-/

open scoped BigOperators ArithmeticFunction.Moebius
open Finset Real Complex ArithmeticFunction

namespace GoldbachWave33

/-! ### Part 1: Klüyver's Integer Formula for Ramanujan's Sum `c_q(m)` -/

/-- Pure integer Klüyver formula for Ramanujan's sum `c_q(m) = ∑_{h ∣ gcd(q, m)} h * μ(q / h)`. -/
def ramanujanSum (q m : ℕ) : ℤ :=
  ∑ h ∈ (Nat.gcd q m).divisors, (h : ℤ) * μ (q / h)

/-- Additive character `e(k / q) = exp(2 * π * I * k / q)`. -/
noncomputable def eFrac (k : ℤ) (q : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (q : ℂ))

private lemma eFrac_add (k₁ k₂ : ℤ) (q : ℕ) : eFrac (k₁ + k₂) q = eFrac k₁ q * eFrac k₂ q := by
  unfold eFrac; rw [← Complex.exp_add]; congr 1; push_cast; ring

private lemma eFrac_pow (k : ℤ) (q m : ℕ) : (eFrac k q) ^ m = eFrac ((m : ℤ) * k) q := by
  induction m with
  | zero => simp [eFrac]
  | succ m ih => rw [pow_succ, ih, ← eFrac_add]; congr 1; push_cast; ring

private lemma eFrac_cancel_mul {k : ℤ} {q c : ℕ} (hc : 0 < c) :
    eFrac ((c : ℤ) * k) (c * q) = eFrac k q := by
  unfold eFrac; congr 1
  have hc_ne : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hc)
  push_cast; field_simp [hc_ne]

private lemma eFrac_eq_one_iff {q : ℕ} (hq : 0 < q) (k : ℤ) :
    eFrac k q = 1 ↔ (q : ℤ) ∣ k := by
  unfold eFrac; rw [Complex.exp_eq_one_iff]
  have hq_ne : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hq)
  have hpi_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  constructor
  · rintro ⟨t, ht⟩; refine ⟨t, ?_⟩
    have h1 : 2 * Real.pi * Complex.I * (k : ℂ) = (t : ℂ) * (2 * Real.pi * Complex.I) * (q : ℂ) := by
      have := congr_arg (fun z => z * (q : ℂ)) ht
      simpa [div_mul_cancel₀ _ hq_ne] using this
    have h2 : (k : ℂ) = (q : ℂ) * (t : ℂ) := by apply mul_left_cancel₀ hpi_ne; linear_combination h1
    exact_mod_cast h2
  · rintro ⟨t, rfl⟩; refine ⟨t, ?_⟩; push_cast; field_simp [hq_ne]

private lemma eFrac_orthogonality {q : ℕ} (hq : 0 < q) (k : ℤ) :
    ∑ j ∈ Finset.range q, eFrac ((j : ℤ) * k) q = if (q : ℤ) ∣ k then (q : ℂ) else 0 := by
  have hpow : ∑ j ∈ Finset.range q, eFrac ((j : ℤ) * k) q = ∑ j ∈ Finset.range q, (eFrac k q) ^ j :=
    Finset.sum_congr rfl fun j _ => (eFrac_pow k q j).symm
  rw [hpow]
  by_cases hdvd : (q : ℤ) ∣ k
  · simp [hdvd, (eFrac_eq_one_iff hq k).mpr hdvd]
  · have hne : eFrac k q ≠ 1 := fun h => hdvd ((eFrac_eq_one_iff hq k).mp h)
    have hpowq : (eFrac k q) ^ q = 1 := by
      rw [eFrac_pow, eFrac_eq_one_iff hq]; exact dvd_mul_right (q : ℤ) k
    have hgeom := geom_sum_mul (eFrac k q) q
    rw [hpowq, sub_self] at hgeom
    have h0 : ∑ j ∈ Finset.range q, (eFrac k q) ^ j = 0 := by
      rcases mul_eq_zero.mp hgeom with h | h
      · exact h
      · exact absurd (sub_eq_zero.mp h) hne
    simp [hdvd, h0]

/-- Key integer divisor-sum identity: `∑_{q ∣ d} ramanujanSum q m = if d ∣ m then d else 0`. -/
lemma sum_divisors_ramanujanSum {d : ℕ} (hd : 0 < d) (m : ℕ) :
    ∑ q ∈ d.divisors, ramanujanSum q m = if d ∣ m then (d : ℤ) else 0 := by
  -- Expand ramanujanSum q m = ∑_{h ∣ q, h ∣ m} h * μ(q / h) and swap sums!
  have hexp : ∑ q ∈ d.divisors, ramanujanSum q m
      = ∑ q ∈ d.divisors, ∑ h ∈ d.divisors, if h ∣ q ∧ h ∣ m then (h : ℤ) * μ (q / h) else 0 := by
    refine Finset.sum_congr rfl fun q hq => ?_
    have hqd : q ∣ d := Nat.dvd_of_mem_divisors hq
    have hq_pos : 0 < q := Nat.pos_of_dvd_of_pos hqd hd
    unfold ramanujanSum
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext h
    simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hhq, hhm⟩, _⟩
      exact ⟨⟨dvd_trans hhq hqd, ne_of_gt hd⟩, hhq, hhm⟩
    · rintro ⟨⟨_, _⟩, hhq, hhm⟩
      exact ⟨⟨hhq, hhm⟩, ne_of_gt (Nat.gcd_pos_of_pos_left m hq_pos)⟩
  rw [hexp, Finset.sum_comm]
  -- For each h ∣ d: if ¬(h ∣ m), inner sum is 0; if h ∣ m, ∑_{q ∣ d, h ∣ q} μ(q / h) = ∑_{r ∣ d / h} μ(r) = 1_{d/h = 1} = 1_{h = d}!
  have hinner : ∀ h ∈ d.divisors,
      (∑ q ∈ d.divisors, if h ∣ q ∧ h ∣ m then (h : ℤ) * μ (q / h) else 0)
        = if h = d ∧ d ∣ m then (d : ℤ) else 0 := by
    intro h hh
    have hhd : h ∣ d := Nat.dvd_of_mem_divisors hh
    have hh_pos : 0 < h := Nat.pos_of_dvd_of_pos hhd hd
    by_cases hhm : h ∣ m
    · have hfilt : (∑ q ∈ d.divisors, if h ∣ q ∧ h ∣ m then (h : ℤ) * μ (q / h) else 0)
          = (h : ℤ) * ∑ r ∈ (d / h).divisors, μ r := by
        rw [← Finset.sum_filter, Finset.mul_sum]
        symm
        refine Finset.sum_bij (fun r _ => h * r) ?_ ?_ ?_ ?_
        · intro r hr
          rw [Nat.mem_divisors] at hr
          rw [Finset.mem_filter, Nat.mem_divisors]
          refine ⟨⟨?_, ne_of_gt hd⟩, dvd_mul_right h r, hhm⟩
          have h1 : h * r ∣ h * (d / h) := Nat.mul_dvd_mul_left h hr.1
          rwa [Nat.mul_div_cancel' hhd] at h1
        · intro r₁ _ r₂ _ heq; exact Nat.eq_of_mul_eq_mul_left hh_pos heq
        · intro q hq
          rw [Finset.mem_filter, Nat.mem_divisors] at hq
          refine ⟨q / h, ?_, Nat.mul_div_cancel' hq.2.1⟩
          rw [Nat.mem_divisors]
          refine ⟨?_, ne_of_gt (Nat.div_pos (Nat.le_of_dvd hd hhd) hh_pos)⟩
          obtain ⟨t, ht⟩ := hq.1.1
          refine ⟨t, ?_⟩
          have hm : h * (d / h) = h * (q / h * t) := by
            rw [Nat.mul_div_cancel' hhd, ← mul_assoc, Nat.mul_div_cancel' hq.2.1, ht]
          exact Nat.eq_of_mul_eq_mul_left hh_pos hm
        · intro r _; rw [Nat.mul_div_cancel_left r hh_pos]
      rw [hfilt]
      -- ∑_{r ∣ d / h} μ r = (ζ * μ) (d / h) = (1 : ArithmeticFunction ℤ) (d / h)!
      have hmu_sum : ∑ r ∈ (d / h).divisors, μ r = if d / h = 1 then 1 else 0 := by
        have hzm := congrArg (fun f : ArithmeticFunction ℤ => f (d / h)) ArithmeticFunction.coe_zeta_mul_moebius
        rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal' (fun a b =>
          ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) a * μ b)] at hzm
        have hrew : ∑ r ∈ (d / h).divisors,
              ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) ((d / h) / r) * μ r
            = ∑ r ∈ (d / h).divisors, μ r := by
          refine Finset.sum_congr rfl fun r hr => ?_
          have hdh_pos : 0 < d / h := Nat.div_pos (Nat.le_of_dvd hd hhd) hh_pos
          have hr_pos : 0 < r := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hr) hdh_pos
          have hne : (d / h) / r ≠ 0 := ne_of_gt (Nat.div_pos (Nat.le_of_dvd hdh_pos (Nat.dvd_of_mem_divisors hr)) hr_pos)
          simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hne]
        rw [hrew] at hzm
        rw [hzm]
        by_cases h1 : d / h = 1
        · simp [h1]
        · simp [h1]
      rw [hmu_sum]
      have hiff : d / h = 1 ↔ h = d := by
        constructor
        · intro h1
          have := Nat.mul_div_cancel' hhd
          rw [h1, mul_one] at this; exact this
        · rintro rfl; exact Nat.div_self hd
      by_cases heq : h = d
      · subst heq; simp [hiff.mpr rfl, hhm]
      · simp [mt hiff.mp heq, heq]
    · have h1 : (∑ q ∈ d.divisors, if h ∣ q ∧ h ∣ m then (h : ℤ) * μ (q / h) else 0) = 0 := by
        refine Finset.sum_eq_zero fun q _ => by simp [hhm]
      rw [h1]
      by_cases heq : h = d
      · subst heq; simp [hhm]
      · simp [heq]
  rw [Finset.sum_congr rfl hinner]
  by_cases hdm : d ∣ m
  · rw [if_pos hdm, Finset.sum_eq_single d]
    · simp [hdm]
    · intro h _ hne; simp [hne]
    · intro hnot; exact absurd (Nat.mem_divisors.mpr ⟨dvd_rfl, ne_of_gt hd⟩) hnot
  · rw [if_neg hdm]
    refine Finset.sum_eq_zero fun h _ => by simp [hdm]

/-- Complex exponential form of Ramanujan's sum `c_q^exp(m) = ∑_{a < q, (a, q) = 1} e(a m / q)`. -/
noncomputable def ramanujanExp (q m : ℕ) : ℂ :=
  ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), eFrac ((a : ℤ) * (m : ℤ)) q

private lemma sum_divisors_ramanujanExp {d : ℕ} (hd : 0 < d) (m : ℕ) :
    ∑ q ∈ d.divisors, ramanujanExp q m = if d ∣ m then (d : ℂ) else 0 := by
  -- Partition range d by gcd(j, d), matching eFrac_orthogonality!
  have hpart : ∑ j ∈ Finset.range d, eFrac ((j : ℤ) * (m : ℤ)) d
      = ∑ q ∈ d.divisors, ramanujanExp q m := by
    have hsig : ∑ q ∈ d.divisors, ramanujanExp q m
        = ∑ p ∈ d.divisors.sigma (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q)),
            eFrac ((p.2 : ℤ) * (m : ℤ)) p.1 :=
      Finset.sum_sigma' d.divisors (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q))
        (fun q a => eFrac ((a : ℤ) * (m : ℤ)) q)
    rw [hsig]
    refine Finset.sum_bij (fun j _ => ⟨d / Nat.gcd j d, j / Nat.gcd j d⟩) ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_range] at hj
      have hg_pos : 0 < Nat.gcd j d := Nat.gcd_pos_of_pos_right j hd
      have hgd : Nat.gcd j d ∣ d := Nat.gcd_dvd_right j d
      rw [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_filter, Finset.mem_range]
      refine ⟨⟨Nat.div_dvd_of_dvd hgd, ne_of_gt hd⟩, ?_, Nat.coprime_div_gcd_div_gcd hg_pos⟩
      have hmul : Nat.gcd j d * (j / Nat.gcd j d) < Nat.gcd j d * (d / Nat.gcd j d) := by
        rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left j d), Nat.mul_div_cancel' hgd]; exact hj
      exact Nat.lt_of_mul_lt_mul_left hmul
    · intro j₁ _ j₂ _ heq
      have h1 : d / Nat.gcd j₁ d = d / Nat.gcd j₂ d := congrArg Sigma.fst heq
      have h2 : j₁ / Nat.gcd j₁ d = j₂ / Nat.gcd j₂ d := by simpa using congrArg Sigma.snd heq
      have hg1_pos : 0 < Nat.gcd j₁ d := Nat.gcd_pos_of_pos_right j₁ hd
      have hgd1 : Nat.gcd j₁ d ∣ d := Nat.gcd_dvd_right j₁ d
      have hgd2 : Nat.gcd j₂ d ∣ d := Nat.gcd_dvd_right j₂ d
      have hq_pos : 0 < d / Nat.gcd j₁ d := Nat.div_pos (Nat.le_of_dvd hd hgd1) hg1_pos
      have hg_eq : Nat.gcd j₁ d = Nat.gcd j₂ d := by
        have hm : Nat.gcd j₁ d * (d / Nat.gcd j₁ d) = Nat.gcd j₂ d * (d / Nat.gcd j₁ d) := by
          rw [Nat.mul_div_cancel' hgd1, h1, Nat.mul_div_cancel' hgd2]
        exact Nat.eq_of_mul_eq_mul_right hq_pos hm
      calc j₁ = Nat.gcd j₁ d * (j₁ / Nat.gcd j₁ d) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left j₁ d)).symm
        _ = Nat.gcd j₂ d * (j₂ / Nat.gcd j₂ d) := by rw [h2, hg_eq]
        _ = j₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_left j₂ d)
    · rintro ⟨q, a⟩ hqa
      rw [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_filter, Finset.mem_range] at hqa
      rcases hqa with ⟨⟨hqd, _⟩, haq, hcop⟩
      let g := d / q
      have hq_pos : 0 < q := Nat.pos_of_dvd_of_pos hqd hd
      have hg_pos : 0 < g := Nat.div_pos (Nat.le_of_dvd hd hqd) hq_pos
      have hqg : g * q = d := by rw [mul_comm]; exact Nat.mul_div_cancel' hqd
      refine ⟨g * a, Finset.mem_range.mpr (by rw [← hqg]; exact Nat.mul_lt_mul_of_pos_left haq hg_pos), ?_⟩
      have hgcd : Nat.gcd (g * a) d = g := by rw [← hqg, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
      ext <;> dsimp only
      · rw [hgcd, ← hqg, Nat.mul_div_cancel_left q hg_pos]
      · rw [hgcd, Nat.mul_div_cancel_left a hg_pos]
    · intro j _
      let c := Nat.gcd j d
      have hc_pos : 0 < c := Nat.gcd_pos_of_pos_right j hd
      have hcj : c * (j / c) = j := Nat.mul_div_cancel' (Nat.gcd_dvd_left j d)
      have hcd : c * (d / c) = d := Nat.mul_div_cancel' (Nat.gcd_dvd_right j d)
      conv_lhs => rw [← hcj, ← hcd]
      have hrew : ((c * (j / c) : ℕ) : ℤ) * (m : ℤ) = (c : ℤ) * (((j / c : ℕ) : ℤ) * (m : ℤ)) := by
        push_cast; ring
      rw [hrew, eFrac_cancel_mul hc_pos]
  rw [← hpart, eFrac_orthogonality hd]
  have hdvd : (d : ℤ) ∣ (m : ℤ) ↔ d ∣ m := Int.natCast_dvd_natCast
  simp [hdvd]

/-- **Theorem 1 (Klüyver's Identity — Exact Complex-to-Integer Equality for Ramanujan's Sum)**:
For every `0 < q` and every `m : ℕ`:
`∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), eFrac (a * m) q = (ramanujanSum q m : ℂ)`! -/
theorem ramanujanSum_eq_complex_exp_sum {q : ℕ} (hq : 0 < q) (m : ℕ) :
    ramanujanExp q m = (ramanujanSum q m : ℂ) := by
  -- Strong induction on q ≥ 1 using sum_divisors_ramanujanExp = sum_divisors_ramanujanSum!
  induction q using Nat.strong_induction_on with
  | h q ih =>
    have h1 := sum_divisors_ramanujanExp hq m
    have h2 : ∑ d ∈ q.divisors, (ramanujanSum d m : ℂ) = if q ∣ m then (q : ℂ) else 0 := by
      have hZ := sum_divisors_ramanujanSum hq m
      have hC := congrArg (fun z : ℤ => (z : ℂ)) hZ
      simpa using hC
    have hsplit1 : ∑ d ∈ q.divisors, ramanujanExp d m
        = ramanujanExp q m + ∑ d ∈ q.properDivisors, ramanujanExp d m := by
      rw [← Nat.cons_self_properDivisors (ne_of_gt hq), Finset.sum_cons]
    have hsplit2 : ∑ d ∈ q.divisors, (ramanujanSum d m : ℂ)
        = (ramanujanSum q m : ℂ) + ∑ d ∈ q.properDivisors, (ramanujanSum d m : ℂ) := by
      rw [← Nat.cons_self_properDivisors (ne_of_gt hq), Finset.sum_cons]
    have hprop_eq : ∑ d ∈ q.properDivisors, ramanujanExp d m
        = ∑ d ∈ q.properDivisors, (ramanujanSum d m : ℂ) := by
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd' := Nat.mem_properDivisors.mp hd
      exact ih d hd'.2 (Nat.pos_of_dvd_of_pos hd'.1 hq)
    rw [hsplit1] at h1
    rw [hsplit2, ← hprop_eq] at h2
    linear_combination h1 - h2

/-! ### Part 2: Ramanujan's Prime Value & Exact Ramanujan = Goldbach Singular Series Identity -/

/-- Exact value of Ramanujan's sum at a prime `p`: `c_p(m) = p - 1` if `p ∣ m`, `-1` if `p ∤ m`. -/
theorem ramanujanSum_prime {p : ℕ} (hp : Nat.Prime p) (m : ℕ) :
    ramanujanSum p m = if p ∣ m then (p : ℤ) - 1 else -1 := by
  unfold ramanujanSum
  by_cases hpm : p ∣ m
  · have hg : Nat.gcd p m = p := Nat.gcd_eq_left hpm
    rw [if_pos hpm, hg, hp.divisors, Finset.sum_pair hp.ne_one.symm, Nat.div_one,
      Nat.div_self hp.pos, ArithmeticFunction.moebius_apply_prime hp, ArithmeticFunction.moebius_apply_one]
    ring
  · have hcop : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hpm
    rw [if_neg hpm, hcop.gcd_eq_one]
    simp [ArithmeticFunction.moebius_apply_prime hp]

/-- Local Goldbach singular-series factor at a prime `p` for even `n` (matching Wave 24). -/
noncomputable def localSingularFactor (n p : ℕ) : ℝ :=
  if p = 2 then 2
  else (1 - 1 / ((p : ℝ) - 1) ^ 2) * (if p ∣ n then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1)

/-- **Theorem 2 (Exact Ramanujan–Hardy–Littlewood Singular-Series Local Identity)**:
For EVERY even `n` and EVERY prime `p`:
`1 + (ramanujanSum p n : ℝ) / ((p : ℝ) - 1)^2 = localSingularFactor n p`! -/
theorem ramanujan_local_euler_eq_goldbach_singular_series {n p : ℕ} (heven : 2 ∣ n) (hp : Nat.Prime p) :
    1 + (ramanujanSum p n : ℝ) / ((p : ℝ) - 1) ^ 2 = localSingularFactor n p := by
  rw [ramanujanSum_prime hp n]
  unfold localSingularFactor
  have hp2 : 2 ≤ p := hp.two_le
  have hp1_ne : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    linarith
  by_cases h2 : p = 2
  · subst h2; simp only [heven, ↓reduceIte]; norm_num
  · have hp3 : 3 ≤ p := by omega
    have hp2_ne : (p : ℝ) - 2 ≠ 0 := by
      have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
      linarith
    simp only [h2, ↓reduceIte]
    by_cases hpn : p ∣ n
    · simp only [hpn, ↓reduceIte]
      push_cast
      field_simp [hp1_ne, hp2_ne]
      ring
    · simp only [hpn, ↓reduceIte]
      push_cast
      field_simp [hp1_ne]
      ring

/-! ### Part 3: Exact Orthogonality & Parseval Energy of Ramanujan Sums on `ℤ / Qℤ` -/

/-- **Theorem 3 (Exact Orthogonality of Ramanujan Sums on `ℤ / Qℤ`)**:
For ANY `0 < Q` and ANY `q₁, q₂ ∣ Q`:
`∑ m ∈ Finset.range Q, ramanujanSum q₁ m * ramanujanSum q₂ m = if q₁ = q₂ then (Q * Nat.totient q₁ : ℤ) else 0`! -/
theorem ramanujan_sum_orthogonality {Q q₁ q₂ : ℕ} (hQ : 0 < Q) (hq₁ : q₁ ∣ Q) (hq₂ : q₂ ∣ Q) :
    ∑ m ∈ Finset.range Q, ramanujanSum q₁ m * ramanujanSum q₂ m
      = if q₁ = q₂ then ((Q * Nat.totient q₁ : ℕ) : ℤ) else 0 := by
  have hq1_pos : 0 < q₁ := Nat.pos_of_dvd_of_pos hq₁ hQ
  have hq2_pos : 0 < q₂ := Nat.pos_of_dvd_of_pos hq₂ hQ
  let c₁ := Q / q₁
  let c₂ := Q / q₂
  have hc1_pos : 0 < c₁ := Nat.div_pos (Nat.le_of_dvd hQ hq₁) hq1_pos
  have hc2_pos : 0 < c₂ := Nat.div_pos (Nat.le_of_dvd hQ hq₂) hq2_pos
  have hc1_eq : c₁ * q₁ = Q := by rw [mul_comm]; exact Nat.mul_div_cancel' hq₁
  have hc2_eq : c₂ * q₂ = Q := by rw [mul_comm]; exact Nat.mul_div_cancel' hq₂
  -- Prove the equality in ℂ using Theorem 1 + eFrac_orthogonality!
  have hC : ((∑ m ∈ Finset.range Q, ramanujanSum q₁ m * ramanujanSum q₂ m : ℤ) : ℂ)
      = ((if q₁ = q₂ then ((Q * Nat.totient q₁ : ℕ) : ℤ) else 0 : ℤ) : ℂ) := by
    have hL : ((∑ m ∈ Finset.range Q, ramanujanSum q₁ m * ramanujanSum q₂ m : ℤ) : ℂ)
        = ∑ m ∈ Finset.range Q, ramanujanExp q₁ m * ramanujanExp q₂ m := by
      push_cast
      refine Finset.sum_congr rfl fun m _ => by
        rw [ramanujanSum_eq_complex_exp_sum hq1_pos, ramanujanSum_eq_complex_exp_sum hq2_pos]
    rw [hL]
    have hexp : ∑ m ∈ Finset.range Q, ramanujanExp q₁ m * ramanujanExp q₂ m
        = ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
          ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
            ∑ m ∈ Finset.range Q, eFrac ((m : ℤ) * ((c₁ : ℤ) * (a₁ : ℤ) + (c₂ : ℤ) * (a₂ : ℤ))) Q := by
      calc ∑ m ∈ Finset.range Q, ramanujanExp q₁ m * ramanujanExp q₂ m
          = ∑ m ∈ Finset.range Q,
              ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
              ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
                eFrac ((m : ℤ) * ((c₁ : ℤ) * (a₁ : ℤ) + (c₂ : ℤ) * (a₂ : ℤ))) Q := by
              refine Finset.sum_congr rfl fun m _ => ?_
              unfold ramanujanExp
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun a₁ _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun a₂ _ => ?_
              have he1 : eFrac ((a₁ : ℤ) * (m : ℤ)) q₁ = eFrac ((m : ℤ) * ((c₁ : ℤ) * (a₁ : ℤ))) Q := by
                rw [← hc1_eq, ← eFrac_cancel_mul hc1_pos]; congr 1; ring
              have he2 : eFrac ((a₂ : ℤ) * (m : ℤ)) q₂ = eFrac ((m : ℤ) * ((c₂ : ℤ) * (a₂ : ℤ))) Q := by
                rw [← hc2_eq, ← eFrac_cancel_mul hc2_pos]; congr 1; ring
              rw [he1, he2, ← eFrac_add]; congr 1; ring
        _ = ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
            ∑ m ∈ Finset.range Q,
            ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
              eFrac ((m : ℤ) * ((c₁ : ℤ) * (a₁ : ℤ) + (c₂ : ℤ) * (a₂ : ℤ))) Q := Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun a₁ _ => Finset.sum_comm
    rw [hexp]
    have hinner : ∀ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
        ∀ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
          (∑ m ∈ Finset.range Q, eFrac ((m : ℤ) * ((c₁ : ℤ) * (a₁ : ℤ) + (c₂ : ℤ) * (a₂ : ℤ))) Q)
            = if q₁ = q₂ ∧ ((a₁ = 0 ∧ a₂ = 0) ∨ a₁ + a₂ = q₁) then (Q : ℂ) else 0 := by
      intro a₁ ha₁ a₂ ha₂
      rw [eFrac_orthogonality hQ]
      have ha1' := Finset.mem_filter.mp ha₁
      have ha2' := Finset.mem_filter.mp ha₂
      have ha1_lt : a₁ < q₁ := Finset.mem_range.mp ha1'.1
      have ha2_lt : a₂ < q₂ := Finset.mem_range.mp ha2'.1
      have hcop1 : Nat.Coprime a₁ q₁ := ha1'.2
      have hcop2 : Nat.Coprime a₂ q₂ := ha2'.2
      have hiff : (Q : ℤ) ∣ ((c₁ : ℤ) * (a₁ : ℤ) + (c₂ : ℤ) * (a₂ : ℤ))
          ↔ q₁ = q₂ ∧ ((a₁ = 0 ∧ a₂ = 0) ∨ a₁ + a₂ = q₁) := by
        constructor
        · intro hdvd
          have hdvdN : Q ∣ c₁ * a₁ + c₂ * a₂ := Int.natCast_dvd_natCast.mp (by exact_mod_cast hdvd)
          -- Show q₁ ∣ q₂ and q₂ ∣ q₁!
          have hq1_dvd_q2 : q₁ ∣ q₂ := by
            -- c₁ * q₁ = Q ∣ c₁ * a₁ + c₂ * a₂ => q₁ ∣ a₁ * q₂ (multiply by q₂/c₁? Simpler: c₂ * q₂ = Q = c₁ * q₁)
            have h1 : Q ∣ (c₁ * a₁ + c₂ * a₂) * q₂ := dvd_mul_of_dvd_left hdvdN q₂
            have h2 : (c₁ * a₁ + c₂ * a₂) * q₂ = c₁ * (a₁ * q₂) + Q * a₂ := by rw [← hc2_eq]; ring
            rw [h2] at h1
            have h3 : Q ∣ c₁ * (a₁ * q₂) := (Nat.dvd_add_left (dvd_mul_right Q a₂)).mp h1
            rw [← hc1_eq] at h3
            have h4 : q₁ ∣ a₁ * q₂ := (Nat.mul_dvd_mul_iff_left hc1_pos).mp h3
            exact hcop1.symm.dvd_of_dvd_mul_left h4
          have hq2_dvd_q1 : q₂ ∣ q₁ := by
            have h1 : Q ∣ (c₁ * a₁ + c₂ * a₂) * q₁ := dvd_mul_of_dvd_left hdvdN q₁
            have h2 : (c₁ * a₁ + c₂ * a₂) * q₁ = Q * a₁ + c₂ * (a₂ * q₁) := by rw [← hc1_eq]; ring
            rw [h2] at h1
            have h3 : Q ∣ c₂ * (a₂ * q₁) := (Nat.dvd_add_right (dvd_mul_right Q a₁)).mp h1
            rw [← hc2_eq] at h3
            have h4 : q₂ ∣ a₂ * q₁ := (Nat.mul_dvd_mul_iff_left hc2_pos).mp h3
            exact hcop2.symm.dvd_of_dvd_mul_left h4
          have hqeq : q₁ = q₂ := Nat.dvd_antisymm hq1_dvd_q2 hq2_dvd_q1
          refine ⟨hqeq, ?_⟩
          have hc_eq : c₁ = c₂ := by dsimp [c₁, c₂]; rw [hqeq]
          rw [← hc_eq, ← mul_add, ← hc1_eq] at hdvdN
          have hq1_dvd_sum : q₁ ∣ a₁ + a₂ := (Nat.mul_dvd_mul_iff_left hc1_pos).mp hdvdN
          obtain ⟨t, ht⟩ := hq1_dvd_sum
          have hlt : a₁ + a₂ < 2 * q₁ := by omega
          have ht_lt : t < 2 := by nlinarith
          interval_cases t
          · left; omega
          · right; omega
        · rintro ⟨rfl, (⟨rfl, rfl⟩ | hsum)⟩
          · simp
          · have hc_eq : c₁ = c₂ := rfl
            rw [← hc_eq]
            have hrew : (c₁ : ℤ) * (a₁ : ℤ) + (c₁ : ℤ) * (a₂ : ℤ) = (c₁ : ℤ) * ((a₁ + a₂ : ℕ) : ℤ) := by
              push_cast; ring
            rw [hrew, hsum]
            have hQeq : (Q : ℤ) = (c₁ : ℤ) * (q₁ : ℤ) := by exact_mod_cast hc1_eq.symm
            rw [hQeq]
      simp [hiff]
    have hsum2 : ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
          ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
            ∑ m ∈ Finset.range Q, eFrac ((m : ℤ) * ((c₁ : ℤ) * (a₁ : ℤ) + (c₂ : ℤ) * (a₂ : ℤ))) Q
        = ∑ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
          ∑ a₂ ∈ (Finset.range q₂).filter (fun a => Nat.Coprime a q₂),
            if q₁ = q₂ ∧ ((a₁ = 0 ∧ a₂ = 0) ∨ a₁ + a₂ = q₁) then (Q : ℂ) else 0 :=
      Finset.sum_congr rfl fun a₁ ha₁ => Finset.sum_congr rfl fun a₂ ha₂ => hinner a₁ ha₁ a₂ ha₂
    rw [hsum2]
    by_cases hqeq : q₁ = q₂
    · subst hqeq
      simp only [true_and, ↓reduceIte]
      -- For each a₁ ∈ {a < q₁ | Coprime a q₁}, there is a UNIQUE partner a₂ = (q₁ - a₁) % q₁!
      have heach : ∀ a₁ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
          (∑ a₂ ∈ (Finset.range q₁).filter (fun a => Nat.Coprime a q₁),
            if (a₁ = 0 ∧ a₂ = 0) ∨ a₁ + a₂ = q₁ then (Q : ℂ) else 0) = (Q : ℂ) := by
        intro a₁ ha₁
        have ha1' := Finset.mem_filter.mp ha₁
        have ha1_lt : a₁ < q₁ := Finset.mem_range.mp ha1'.1
        by_cases ha0 : a₁ = 0
        · subst ha0
          rw [Finset.sum_eq_single 0]
          · simp
          · intro a₂ ha₂ hne; have := Finset.mem_range.mp (Finset.mem_filter.mp ha₂).1; simp [hne]; omega
          · intro hnot; exact absurd ha₁ hnot
        · rw [Finset.sum_eq_single (q₁ - a₁)]
          · have hadd : a₁ + (q₁ - a₁) = q₁ := by omega
            simp [hadd]
          · intro a₂ ha₂ hne; have := Finset.mem_range.mp (Finset.mem_filter.mp ha₂).1
            rw [if_neg]; push Not; exact ⟨fun h => absurd h ha0, by omega⟩
          · intro hnot
            exfalso; apply hnot
            rw [Finset.mem_filter, Finset.mem_range]
            refine ⟨by omega, ?_⟩
            -- Coprime (q₁ - a₁) q₁ follows from Coprime a₁ q₁!
            rw [Nat.coprime_comm]
            have hcop_sym : Nat.Coprime q₁ a₁ := ha1'.2.symm
            rw [Nat.coprime_iff_gcd_eq_one] at hcop_sym ⊢
            have hg : Nat.gcd q₁ (q₁ - a₁) ∣ Nat.gcd q₁ a₁ := by
              refine Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ?_
              have h1 : Nat.gcd q₁ (q₁ - a₁) ∣ q₁ := Nat.gcd_dvd_left _ _
              have h2 : Nat.gcd q₁ (q₁ - a₁) ∣ q₁ - a₁ := Nat.gcd_dvd_right _ _
              have hsub_dvd : Nat.gcd q₁ (q₁ - a₁) ∣ q₁ - (q₁ - a₁) := Nat.dvd_sub h1 h2
              rwa [show q₁ - (q₁ - a₁) = a₁ by omega] at hsub_dvd
            rw [hcop_sym] at hg
            exact Nat.eq_one_of_dvd_one hg
      rw [Finset.sum_congr rfl heach, Finset.sum_const, nsmul_eq_mul]
      have htot : ((Finset.range q₁).filter (fun a => Nat.Coprime a q₁)).card = Nat.totient q₁ := by
        rw [Nat.totient_eq_card_coprime]
        congr 1; ext a; simp [Nat.coprime_comm]
      rw [htot]; push_cast; ring
    · simp only [hqeq, false_and, ↓reduceIte, Finset.sum_const_zero, Int.cast_zero]
  exact_mod_cast hC

/-! ### Part 4: Purely Real Finite Ramanujan Expansion & Parseval Energy -/

/-- **Theorem 4 (Purely Real Exact Finite Ramanujan Expansion of `∑_{d ∈ S, d ∣ x} μ(d)`)**:
For ANY `D_max : ℕ`, ANY `S ⊆ Finset.Icc 1 D_max`, and ANY `x : ℕ`:
`∑ d ∈ S.filter (· ∣ x), (μ d : ℝ)`
`= ∑ q ∈ Finset.Icc 1 D_max, ((μ q : ℝ) / q) * (∑ m ∈ (Finset.Icc 1 (D_max / q)).filter (fun m => q * m ∈ S ∧ Nat.Coprime m q), (μ m : ℝ) / m) * (ramanujanSum q x : ℝ)`!
Zero complex numbers — pure integer Klüyver identity + Möbius coprime splitting! -/
theorem divisor_moebius_ramanujan_expansion_exact {D_max : ℕ} (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 D_max) (x : ℕ) :
    ∑ d ∈ S.filter (· ∣ x), (μ d : ℝ)
      = ∑ q ∈ Finset.Icc 1 D_max,
          ((μ q : ℝ) / (q : ℝ)) *
          (∑ m ∈ (Finset.Icc 1 (D_max / q)).filter (fun m => q * m ∈ S ∧ Nat.Coprime m q),
            ((μ m : ℝ) / (m : ℝ))) *
          (ramanujanSum q x : ℝ) := by
  have hsingle : ∀ d ∈ S,
      (if d ∣ x then (μ d : ℝ) else 0)
        = ((μ d : ℝ) / (d : ℝ)) * ∑ q ∈ d.divisors, (ramanujanSum q x : ℝ) := by
    intro d hd
    have hd_pos : 0 < d := (Finset.mem_Icc.mp (hS hd)).1
    have hd_ne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hd_pos)
    have hsumR : ∑ q ∈ d.divisors, (ramanujanSum q x : ℝ) = if d ∣ x then (d : ℝ) else 0 := by
      have hZ := sum_divisors_ramanujanSum hd_pos x
      have hR := congrArg (fun z : ℤ => (z : ℝ)) hZ
      simpa using hR
    rw [hsumR]
    split_ifs <;> [field_simp [hd_ne]; ring]
  rw [Finset.sum_filter]
  have hL : ∑ d ∈ S, (if d ∣ x then (μ d : ℝ) else 0)
      = ∑ d ∈ S, ∑ q ∈ Finset.Icc 1 D_max,
          if q ∣ d then ((μ d : ℝ) / (d : ℝ)) * (ramanujanSum q x : ℝ) else 0 := by
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [hsingle d hd, Finset.mul_sum, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    have hd_icc := Finset.mem_Icc.mp (hS hd)
    ext q
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hqd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hqd hd_icc.1, le_trans (Nat.le_of_dvd hd_icc.1 hqd) hd_icc.2⟩, hqd⟩
    · rintro ⟨_, hqd⟩
      exact ⟨hqd, by omega⟩
  rw [hL, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq_icc := Finset.mem_Icc.mp hq
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_filter]
  have hnoncop0 : ∑ d ∈ S.filter (fun d => q ∣ d), ((μ d : ℝ) / (d : ℝ)) * (ramanujanSum q x : ℝ)
      = ∑ d ∈ S.filter (fun d => q ∣ d ∧ Nat.Coprime (d / q) q),
          ((μ d : ℝ) / (d : ℝ)) * (ramanujanSum q x : ℝ) := by
    symm
    refine Finset.sum_subset (fun d hd => by rw [Finset.mem_filter] at hd ⊢; exact ⟨hd.1, hd.2.1⟩) ?_
    intro d hd hnot
    rw [Finset.mem_filter] at hd hnot
    have hnc : ¬Nat.Coprime (d / q) q := fun h => hnot ⟨hd.1, hd.2, h⟩
    have hmu0 : μ d = 0 := by
      have hdeq : d = q * (d / q) := (Nat.mul_div_cancel' hd.2).symm
      rw [hdeq]
      obtain ⟨p, hp, hpq, hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp (fun h => hnc h.symm)
      have hns : ¬Squarefree (q * (d / q)) := fun hsf => hp.not_isUnit (hsf p (Nat.mul_dvd_mul hpq hpm))
      exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns
    simp [hmu0]
  rw [hnoncop0]
  symm
  refine Finset.sum_bij (fun m _ => q * m) ?_ ?_ ?_ ?_
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    rw [Finset.mem_filter]
    refine ⟨hm.2.1, dvd_mul_right q m, ?_⟩
    rw [Nat.mul_div_cancel_left m hq_icc.1]; exact hm.2.2
  · intro m₁ _ m₂ _ heq; exact Nat.eq_of_mul_eq_mul_left hq_icc.1 heq
  · intro d hd
    rw [Finset.mem_filter] at hd
    have hd_icc := Finset.mem_Icc.mp (hS hd.1)
    refine ⟨d / q, ?_, Nat.mul_div_cancel' hd.2.1⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.div_pos (Nat.le_of_dvd hd_icc.1 hd.2.1) hq_icc.1, Nat.div_le_div_right hd_icc.2⟩,
      by rw [Nat.mul_div_cancel' hd.2.1]; exact hd.1, hd.2.2⟩
  · intro m hm
    rw [Finset.mem_filter] at hm
    have hmu : μ (q * m) = μ q * μ m :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hm.2.2.symm
    rw [hmu]; push_cast; ring

/-- **Theorem 5 (Exact Ramanujan Parseval Energy Identity on `ℤ / Qℤ`)**:
For ANY `0 < Q` and ANY real Ramanujan coefficients `α : ℕ → ℝ`:
`∑ m ∈ Finset.range Q, (∑ q ∈ Q.divisors, α q * (ramanujanSum q m : ℝ)) ^ 2`
`= (Q : ℝ) * ∑ q ∈ Q.divisors, (Nat.totient q : ℝ) * (α q) ^ 2`! -/
theorem ramanujan_parseval_energy {Q : ℕ} (hQ : 0 < Q) (α : ℕ → ℝ) :
    ∑ m ∈ Finset.range Q, (∑ q ∈ Q.divisors, α q * (ramanujanSum q m : ℝ)) ^ 2
      = (Q : ℝ) * ∑ q ∈ Q.divisors, (Nat.totient q : ℝ) * (α q) ^ 2 := by
  calc ∑ m ∈ Finset.range Q, (∑ q ∈ Q.divisors, α q * (ramanujanSum q m : ℝ)) ^ 2
      = ∑ m ∈ Finset.range Q,
          ∑ q₁ ∈ Q.divisors, ∑ q₂ ∈ Q.divisors,
            α q₁ * α q₂ * ((ramanujanSum q₁ m : ℝ) * (ramanujanSum q₂ m : ℝ)) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [sq, Finset.sum_mul]
          refine Finset.sum_congr rfl fun q₁ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun q₂ _ => by ring
    _ = ∑ q₁ ∈ Q.divisors, ∑ m ∈ Finset.range Q, ∑ q₂ ∈ Q.divisors,
          α q₁ * α q₂ * ((ramanujanSum q₁ m : ℝ) * (ramanujanSum q₂ m : ℝ)) := Finset.sum_comm
    _ = ∑ q₁ ∈ Q.divisors, ∑ q₂ ∈ Q.divisors, ∑ m ∈ Finset.range Q,
          α q₁ * α q₂ * ((ramanujanSum q₁ m : ℝ) * (ramanujanSum q₂ m : ℝ)) := by
          refine Finset.sum_congr rfl fun q₁ _ => Finset.sum_comm
    _ = ∑ q₁ ∈ Q.divisors, ∑ q₂ ∈ Q.divisors,
          α q₁ * α q₂ * ∑ m ∈ Finset.range Q, ((ramanujanSum q₁ m : ℝ) * (ramanujanSum q₂ m : ℝ)) := by
          refine Finset.sum_congr rfl fun q₁ _ => Finset.sum_congr rfl fun q₂ _ => by rw [← Finset.mul_sum]
    _ = ∑ q₁ ∈ Q.divisors, (Q : ℝ) * ((Nat.totient q₁ : ℝ) * (α q₁) ^ 2) := by
          refine Finset.sum_congr rfl fun q₁ hq₁ => ?_
          have hq1_dvd : q₁ ∣ Q := Nat.dvd_of_mem_divisors hq₁
          rw [Finset.sum_eq_single q₁]
          · have horth := ramanujan_sum_orthogonality hQ hq1_dvd hq1_dvd
            have hR : ∑ m ∈ Finset.range Q, ((ramanujanSum q₁ m : ℝ) * (ramanujanSum q₁ m : ℝ))
                = (Q : ℝ) * (Nat.totient q₁ : ℝ) := by
              have := congrArg (fun z : ℤ => (z : ℝ)) horth
              simpa using this
            rw [hR]; ring
          · intro q₂ hq₂ hne
            have hq2_dvd : q₂ ∣ Q := Nat.dvd_of_mem_divisors hq₂
            have horth := ramanujan_sum_orthogonality hQ hq1_dvd hq2_dvd
            have hR : ∑ m ∈ Finset.range Q, ((ramanujanSum q₁ m : ℝ) * (ramanujanSum q₂ m : ℝ)) = 0 := by
              have := congrArg (fun z : ℤ => (z : ℝ)) horth
              simpa [hne.symm] using this
            rw [hR, mul_zero]
          · intro hnot; exact absurd hq₁ hnot
    _ = (Q : ℝ) * ∑ q ∈ Q.divisors, (Nat.totient q : ℝ) * (α q) ^ 2 := by rw [← Finset.mul_sum]

end GoldbachWave33

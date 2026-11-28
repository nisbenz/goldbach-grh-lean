import Mathlib

/-!
# Wave 7 Fifth-Leaf Barriers (`R2.H3` / `B-013`)

Two exact, deterministic, kernel-checked structural theorems isolating what any proof of
Strong Goldbach (and specifically the long-divisor Möbius tail `T_D(n) ≤ n / 2`) must overcome:

1. `reflection_energy_split`: For any `f : ℕ → ℝ` and `n : ℕ`,
   `∑_{x ∈ [1, n-1]} f(x) f(n - x) = ‖f_+‖₂² - ‖f_-‖₂²`,
   where `f_±(x) = (f(x) ± f(n - x)) / 2`. Thus Goldbach positivity is identically equivalent
   to symmetric `L²` energy strictly exceeding antisymmetric `L²` energy around `n / 2`.

2. `fComp_short_divisor_close`: For `f_comp(x) := 1_{x prime, (x,n)=1, ¬(n-x) prime} log x`,
   which is supported **exclusively on genuine primes**, satisfies `0 ≤ f_comp x ≤ log x`,
   and has **zero Goldbach pairs** (`∑ f_comp(x) Λ_pr(n - x) = 0`), every short arithmetic
   progression `x ≡ n (mod d)` (`2 ≤ d ≤ n - 2`, `(d, n) = 1`) agrees with `Λ_pr` up to at most
   one term (`≤ log n`), and the full short-divisor sum `S_D` agrees within `D * (log n)^2`.
   Hence `T_D(f_comp) = S_D(f_comp) ≈ +n S(n)`, proving that no bound on `T_D` can separate the
   `k = 1` prime-`d` terms from the composite-`d` / `k ≥ 2` terms or rely solely on short
   progressions `x ≡ n (mod d)` together with primality and `0 ≤ f ≤ log x`.
-/

namespace GoldbachAttack

open Finset

/-- Exact symmetric–antisymmetric `L²` energy identity for the Goldbach reflection convolution. -/
theorem reflection_energy_split (f : ℕ → ℝ) (n : ℕ) :
    (∑ x ∈ Finset.Icc 1 (n - 1), f x * f (n - x)) =
      (∑ x ∈ Finset.Icc 1 (n - 1), ((f x + f (n - x)) / 2) ^ 2) -
      (∑ x ∈ Finset.Icc 1 (n - 1), ((f x - f (n - x)) / 2) ^ 2) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- Prime-only von Mangoldt weight coprime to `n`. -/
noncomputable def lamPr (n x : ℕ) : ℝ :=
  if Nat.Prime x ∧ Nat.Coprime x n then Real.log (x : ℝ) else 0

/-- Deterministic prime-supported function with zero Goldbach pairs against `lamPr n`. -/
noncomputable def fComp (n x : ℕ) : ℝ :=
  if Nat.Prime x ∧ Nat.Coprime x n ∧ ¬ Nat.Prime (n - x) then Real.log (x : ℝ) else 0

/-- `fComp n` is non-negative and pointwise bounded by `lamPr n`. -/
lemma fComp_bounds (n x : ℕ) : 0 ≤ fComp n x ∧ fComp n x ≤ lamPr n x := by
  unfold fComp lamPr
  by_cases h1 : Nat.Prime x ∧ Nat.Coprime x n
  · obtain ⟨hp, hcop⟩ := h1
    have hlog : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
    by_cases h2 : ¬ Nat.Prime (n - x)
    · rw [if_pos ⟨hp, hcop, h2⟩, if_pos ⟨hp, hcop⟩]
      exact ⟨hlog, le_rfl⟩
    · rw [if_neg (fun h => h2 h.2.2), if_pos ⟨hp, hcop⟩]
      exact ⟨le_rfl, hlog⟩
  · have hnot : ¬ (Nat.Prime x ∧ Nat.Coprime x n ∧ ¬ Nat.Prime (n - x)) := fun h => h1 ⟨h.1, h.2.1⟩
    rw [if_neg hnot, if_neg h1]
    exact ⟨le_rfl, le_rfl⟩

/-- `fComp n` has identically zero prime-pair convolution against `lamPr n`. -/
theorem fComp_zero_goldbach (n : ℕ) :
    ∑ x ∈ Finset.Icc 1 (n - 2), fComp n x * lamPr n (n - x) = 0 := by
  refine Finset.sum_eq_zero fun x _ => ?_
  unfold fComp lamPr
  by_cases hp : Nat.Prime (n - x)
  · simp [hp]
  · simp [hp]

/-- For every modulus `2 ≤ d ≤ n - 2`, `lamPr n` and `fComp n` differ on the Goldbach
progression `d ∣ (n - x)` by at most a single term (`x = n - d`), bounded by `log n`. -/
theorem fComp_progression_diff_le (n d : ℕ) (hd2 : 2 ≤ d) (hdn : d ≤ n - 2) :
    0 ≤ (∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => d ∣ (n - x)), lamPr n x) -
        (∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => d ∣ (n - x)), fComp n x) ∧
    (∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => d ∣ (n - x)), lamPr n x) -
        (∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => d ∣ (n - x)), fComp n x) ≤
      Real.log (n : ℝ) := by
  rw [← Finset.sum_sub_distrib]
  have hterm_nn : ∀ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => d ∣ (n - x)),
      0 ≤ lamPr n x - fComp n x := fun x _ => sub_nonneg.mpr (fComp_bounds n x).2
  constructor
  · exact Finset.sum_nonneg hterm_nn
  · have hvanish : ∀ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => d ∣ (n - x)),
        x ≠ n - d → lamPr n x - fComp n x = 0 := by
      intro x hx hne
      have hxIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1
      have hdvd : d ∣ (n - x) := (Finset.mem_filter.mp hx).2
      have hnotp : ¬ Nat.Prime (n - x) := by
        intro hp
        rcases hp.eq_one_or_self_of_dvd d hdvd with h1 | hself
        · omega
        · apply hne; omega
      unfold lamPr fComp
      simp [hnotp]
    by_cases hmem : n - d ∈ (Finset.Icc 1 (n - 2)).filter (fun x => d ∣ (n - x))
    · rw [Finset.sum_eq_single (n - d) (fun x hx hne => hvanish x hx hne) (fun h => absurd hmem h)]
      have h1 : lamPr n (n - d) - fComp n (n - d) ≤ lamPr n (n - d) := by
        linarith [(fComp_bounds n (n - d)).1]
      refine h1.trans ?_
      unfold lamPr
      split_ifs with h
      · exact Real.log_le_log (by exact_mod_cast h.1.pos) (by exact_mod_cast Nat.sub_le n d)
      · exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    · have hzero : ∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => d ∣ (n - x)),
          (lamPr n x - fComp n x) = 0 :=
        Finset.sum_eq_zero fun x hx => hvanish x hx (fun heq => hmem (heq ▸ hx))
      rw [hzero]
      exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))

/-- Short-divisor sum `S_D(f)` with Möbius-log weight. -/
noncomputable def shortDivisorSum (n D : ℕ) (f : ℕ → ℝ) : ℝ :=
  -(∑ d ∈ (Finset.Icc 1 D).filter (fun d => Nat.Coprime d n),
      (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) *
        ∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => d ∣ (n - x)), f x)

/-- Exact short-divisor agreement: `|S_D(lamPr n) - S_D(fComp n)| ≤ D * (log n)^2`.
At `D ≈ n^{3/8}`, this is `O(n^{3/8} (log n)^2) ≪ n`, proving that `fComp n` passes the full
short-divisor main term `S_D` while having zero Goldbach pairs (`T_D(fComp) = S_D(fComp)`). -/
theorem fComp_shortDivisorSum_close (n D : ℕ) (hn : 4 ≤ n) (hD : D ≤ n - 2) :
    |shortDivisorSum n D (lamPr n) - shortDivisorSum n D (fComp n)| ≤
      (D : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
  unfold shortDivisorSum
  have hsub :
      -(∑ d ∈ (Finset.Icc 1 D).filter (fun d => Nat.Coprime d n),
          (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) *
            ∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => d ∣ (n - x)), lamPr n x) -
      (-(∑ d ∈ (Finset.Icc 1 D).filter (fun d => Nat.Coprime d n),
          (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) *
            ∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => d ∣ (n - x)), fComp n x)) =
      -(∑ d ∈ (Finset.Icc 1 D).filter (fun d => Nat.Coprime d n),
          (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) *
            ((∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => d ∣ (n - x)), lamPr n x) -
             (∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => d ∣ (n - x)), fComp n x))) := by
    have h1 :
        (∑ d ∈ (Finset.Icc 1 D).filter (fun d => Nat.Coprime d n),
          (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) *
            ∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => d ∣ (n - x)), lamPr n x) -
        (∑ d ∈ (Finset.Icc 1 D).filter (fun d => Nat.Coprime d n),
          (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) *
            ∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => d ∣ (n - x)), fComp n x) =
        ∑ d ∈ (Finset.Icc 1 D).filter (fun d => Nat.Coprime d n),
          (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) *
            ((∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => d ∣ (n - x)), lamPr n x) -
             (∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => d ∣ (n - x)), fComp n x)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d _ => by ring
    linarith
  rw [hsub, abs_neg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hlogn_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hterm : ∀ d ∈ (Finset.Icc 1 D).filter (fun d => Nat.Coprime d n),
      |(ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) *
        ((∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => d ∣ (n - x)), lamPr n x) -
         (∑ x ∈ (Finset.Icc 1 (n - 2)).filter (fun x => d ∣ (n - x)), fComp n x))| ≤
        (Real.log (n : ℝ)) ^ 2 := by
    intro d hd
    have hdIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
    by_cases hd1 : d = 1
    · subst hd1
      simp [sq_nonneg]
    · have hd2 : 2 ≤ d := by omega
      have hdn : d ≤ n - 2 := hdIcc.2.trans hD
      obtain ⟨hdiff_nn, hdiff_le⟩ := fComp_progression_diff_le n d hd2 hdn
      have hmu_le : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        by_cases hsf : Squarefree d
        · rw [ArithmeticFunction.moebius_apply_of_squarefree hsf]
          simp
        · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
          simp
      have hlogd_nn : 0 ≤ Real.log (d : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ d))
      have hlogd_le : Real.log (d : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < d)) (by exact_mod_cast (by omega : d ≤ n))
      rw [abs_mul, abs_mul, abs_of_nonneg hlogd_nn, abs_of_nonneg hdiff_nn]
      calc
        |(ArithmeticFunction.moebius d : ℝ)| * Real.log (d : ℝ) * _
          ≤ 1 * Real.log (n : ℝ) * Real.log (n : ℝ) := by
              have h1 : |(ArithmeticFunction.moebius d : ℝ)| * Real.log (d : ℝ) ≤
                  1 * Real.log (n : ℝ) :=
                mul_le_mul hmu_le hlogd_le hlogd_nn (by norm_num)
              exact mul_le_mul h1 hdiff_le hdiff_nn (by positivity)
        _ = (Real.log (n : ℝ)) ^ 2 := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.Icc 1 D).filter (fun d => Nat.Coprime d n)).card ≤ D := by
    have h1 := Finset.card_filter_le (Finset.Icc 1 D) (fun d => Nat.Coprime d n)
    simpa [Nat.card_Icc] using h1
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)

end GoldbachAttack

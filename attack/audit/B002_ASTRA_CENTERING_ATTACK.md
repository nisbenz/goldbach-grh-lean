# B-002 · What centering proves at one even target

[P] Astra (astra-b002), 27 November 2026. Tags apply through the end of their paragraph, displayed equation, table, or code block. [Q] identifies repository inputs, [P] a derivation or computation in this audit, [I] an interpretation, and [U] an additional hypothesis, prediction, or outstanding result.

[U] **B-002 is open under ERH** (Dirichlet GRH, including conductor one). The finite identities are exact. The sum of their two energies measures the size of the weights. Their difference requires estimating the overlap of the weights with their reflection at the specified target. There is an unconditional negative main term for the **average** difference, derived below. A pointwise asymptotic for the difference, with a normalized error tending to zero at every even target, would imply binary Goldbach for all sufficiently large even integers.

## 1. Equation (6) and the RH margin

[P] Fix an integer \(N>1\), let \(J=\{1,\ldots,N-1\}\), \(rj=N-j\), \(V=\{j\in J:(j,N)=1\}\), \(\kappa=N/\varphi(N)\), \(v_j=\kappa 1_V(j)\), and \(h_j=\Lambda(j)-v_j\). Use ordered pairs and put \(R_N=\sum_J\Lambda(j)\Lambda(rj)\). In the exponential normalization, extracting frequency \(N\) leaves exactly these pairs, each with weight \(\exp[-(j+rj)/N]=e^{-1}\). Absolute convergence follows from \(\Lambda(j)\le\log j\) and exponential decay. Thus \(eF_N(\mathbb T)=R_N\).

[P] Reflection permutes \(V\), since \(\gcd(N-j,N)=\gcd(j,N)\). Both mixed sums in the expansion of \(U_N=\sum_J h_jh_{rj}\) equal \(\kappa\sum_V\Lambda(j)\). The reference-reference term equals \(\kappa^2\varphi(N)=\kappa N\). Writing \(\psi(x)=\sum_{m\le x}\Lambda(m)\) gives the two identities
\[
 \psi_{\rm unit}(N)=\sum_V\Lambda(j)
   =\psi(N)-\sum_{p\mid N}\#\{b\ge1:p^b\le N\}\log p,\qquad
 R_N=U_N+2\kappa\psi_{\rm unit}(N)-\kappa N.
\]
[P] This also handles \(j=N\) in the inclusive \(\psi\): if it carries positive weight, its prime divides \(N\), and the subtraction removes it. For \(h_j^\pm=(h_j\pm h_{rj})/2\), the identity \(((a+b)/2)^2-((a-b)/2)^2=ab\) holds even at the fixed point \(j=N/2\). Summation gives \(E_+-E_-=U_N\), where \(E_\pm=\sum_J(h_j^\pm)^2\). Summing the addition identity gives \(E_++E_-=\sum_J h_j^2\) by the permutation of \(J\).

[Q] Theorem 3 quotes Schoenfeld's RH estimate \(|\psi(x)-x|\le\sqrt{x}\log^2(x)/(8\pi)\) for \(x\ge73.2\). Equation (1) charges all pairs involving a higher prime power at most \(e b_N=2.85240\sqrt N\log N\) in the \(R_N\) normalization. Its underlying prime-power estimate and the external finite verification at \(C=4\cdot10^{18}\) are inputs. [Source](../../proof/strong_goldbach_research.md#5-attack-4--centering-on-the-targets-reduced-residues)

[P] Write \(L=\log N\). Removed powers cost at most \(L\) per prime, and there are at most \(L/\log2\) distinct primes. Under the quoted inputs, the prime-only mass divided by \(\kappa N\) is at least
\[
 1+\frac{U_N}{\kappa N} -
 \left(\frac{L^2}{4\pi\sqrt N}+\frac{2L^2}{N\log 2}
                 +\frac{2.85240 L}{\kappa\sqrt N}\right).
\]
For even \(N\), use \(\kappa\ge2\). Each resulting envelope \(L^a/N^b\) decreases for \(L>a/b\); the largest such cutoff here is 4. At \(C\), the upper envelope with \(\kappa=2\) lies in the rational interval
\[
 [103542532892,\ 103542532893]\cdot 10^{-18}
   \ \subset\ (0,\,1.05\cdot10^{-7}).
\]
The gap to the threshold exceeds \(1.457467107\cdot10^{-9}\) by strict outward rounding. Thus a **nonstrict** H3 bound gives **strictly positive** prime mass. The arithmetic certifies a bound on the loss, independently of whether RH holds. The certificate in the appendix encloses logarithms by a positive series with geometric tail and \(\pi\) by Machin's identity and alternating series.

## 2. Genuine von Mangoldt weights through 50,000

[P] The scan covers **every even \(4\le N\le50000\)**. For each prime \(p\), it assigns \(\log p\) to every \(p^b\), \(b\ge1\). It marks units from the prime divisors of the target, uses its integer totient, and sums the two squares and the signed product separately in extended floating point. Both identities were tested on every row with absolute tolerance \(10^{-12}\kappa N\). An independent Python calculation using trial division, gcd, all \(N-1\) indices and compensated summation reproduced eleven selected rows, including the global minimum, to \(10^{-11}\kappa N\). These are empirical values. H3 concerns \(N>C\); the threshold is shown here for scale.

[P] For \(u_N=U_N/(\kappa N)\), the overall median is −0.304039. The minimum exceeds the model value −1 by 0.543465 and the H3 threshold −0.999999895 by 0.543465 (rounded). The energy ratio \(E_+/E_-\) has median 0.824443. In the table, “mean error” is the mean absolute difference between \(u_N\) and the singular-series prediction in §3. Family rows overlap.

| [P] Targets | Count | Minimum \(u_N\) (target) | Median | Maximum \(u_N\) (target) | Negative | Mean error |
|---|---:|---:|---:|---:|---:|---:|
| All | 24,999 | −0.456535 (4294) | −0.304039 | 0.583957 (6) | 24,967 | 0.016819 |
| \(N\ge10000\) | 20,001 | −0.410885 (13892) | −0.308073 | 0.005023 (30030) | 20,000 | 0.013754 |
| \(2^k,\ k\ge3\) | 13 | −0.396192 (2048) | −0.292301 | 0.226521 (16) | 11 | 0.135136 |
| \(2p^2,\ p\) odd prime | 36 | −0.394869 (1682) | −0.328750 | 0.104590 (18) | 35 | 0.035152 |
| \(30\mid N\) | 1,666 | −0.115102 (2160) | −0.054393 | 0.151407 (30) | 1,656 | 0.011846 |
| \(210\mid N\) | 238 | −0.094161 (15750) | −0.030731 | 0.036300 (210) | 233 | 0.010979 |
| \(2310\mid N\) | 21 | −0.039201 (48510) | −0.020937 | 0.005023 (30030) | 20 | 0.009483 |
| \(30030\mid N\) | 1 | 0.005023 (30030) | 0.005023 | 0.005023 (30030) | 0 | 0.022724 |

| [P] \(N\) | \(U_N\) | \(E_+\) | \(E_-\) | \(E_+/E_-\) | \(u_N\) | Predicted \(u_N\) |
|---:|---:|---:|---:|---:|---:|---:|
| 4294 | −4,175.49 | 9,094.75 | 13,270.24 | 0.68535 | −0.456535 | −0.337742 |
| 30030 | 786.42 | 61,726.36 | 60,939.94 | 1.01290 | 0.005023 | −0.017701 |
| 32768 | −21,274.50 | 109,968.05 | 131,242.55 | 0.83790 | −0.324623 | −0.339838 |
| \(49298=2\cdot157^2\) | −31,884.94 | 175,459.85 | 207,344.79 | 0.84622 | −0.321330 | −0.339811 |
| 50000 | −37,836.10 | 163,489.21 | 201,325.31 | 0.81206 | −0.302689 | −0.295827 |

## 3. Asymptotics, signs and arithmetic structure

[P] Exactly,
\[
 u_N=\frac{R_N}{\kappa N}-1-2\frac{\psi_{\rm unit}(N)-N}{N}.
\]
By the ordinary prime number theorem and the elementary bound for removed powers, the last term is \(o(1)\), uniformly as \(N\to\infty\). A pointwise formula for \(u_N\) with \(o(1)\) error therefore has the same content as the corresponding normalized formula for \(R_N\).

[U] The binary Hardy–Littlewood prediction is \(R_N\sim\mathfrak S(N)N\) along the even integers. [P] At an odd prime not dividing \(N\) the two coordinates forbid two distinct residues, giving \((1-2/p)/(1-1/p)^2=1-1/(p-1)^2\). At \(p\mid N\) the forbidden residues coincide and the local factor is \(p/(p-1)\). The factor at 2 for an even target is 2. Dividing the product by \(\kappa\) cancels **all** the factors at \(p\mid N\), leaving
\[
 \mathfrak S(N)/\kappa = \prod_{p>2,\ p\nmid N}(1-1/(p-1)^2)
  = C_2\prod_{p>2,\ p\mid N}(1+1/[p(p-2)]),\quad
 C_2=\prod_{p>2}(1-1/(p-1)^2).
\]
The product is in \([C_2,1)\) and \(C_2\simeq0.660162\). The scan uses this numerical constant for its descriptive benchmark only. [U] The predicted normalized difference is consequently between about −0.339838 and zero, up to \(o(1)\). It approaches −0.339838 on powers of two and on \(2p^2\) as \(p\to\infty\). It approaches zero along primorials. An additive \(o(1)\) prediction does not determine the sign near zero or a relative asymptotic for a difference with vanishing normalized main term.

[P] **An unconditional average for the difference.** With \(A=\prod_{p>2}(1+1/[p(p-1)])>1\), the ordinary prime number theorem yields
\[
 \sum_{\substack{4\le N\le X\\2\mid N}} U_N=(1-A)X^2/2+o(X^2).
\]
Indeed \(\sum_{N\le X} R_N=\sum_{j<X}\Lambda(j)\psi(X-j)=X^2/2+o(X^2)\): replacing \(\psi(t)\) by \(t\) costs \(o(X^2)\) since \(\sup_{0\le t\le X}|\psi(t)-t|=o(X)\), and the linear term follows by partial summation. Odd totals require an even prime power in one coordinate and contribute \(O(X\log X)\). For \(N=2m\), write \(\kappa(2m)=2\sum_{d\mid m} b(d)\) with \(b(d)=1/\varphi(d)\) for odd squarefree \(d\), zero otherwise. Then \(\sum b(d)/d=A\) by absolute convergence. For fixed \(d\), \(\sum_{m\le X/2,\ d\mid m}m\sim X^2/(8d)\), bounded above by \(X^2/(4d)\) for every \(d\). Dominated convergence gives \(\sum_{2\mid N\le X}\kappa(N)N\sim AX^2/2\). Since \(\psi_{\rm unit}(N)=N+o(N)\), summing the mixed-term error costs \(o(X^2)\) by the same bound. Substitute in (6). This computes a weighted aggregate of \(u_N\); the theorem gives no lower bound on its minimum.

[P] **Individual energies on the two sparse families.** On powers of two and on twice an odd prime square, one can in fact prove unconditionally that each energy is asymptotic to \(N\log N/2\) and their ratio tends to 1. First, PNT and partial summation give \(\sum_{j<N}\Lambda(j)^2\sim N\log N\) (use primes for the main term, while squares and higher powers contribute \(O(\sqrt N\log^3 N)\)). Expanding \(\sum h_j^2\) changes this by \(O(N)\) on these families since \(\kappa\le3\). Next fix an odd primorial \(W\) (the product of the odd primes through a cutoff). Terms with \((N-j,W)>1\) in \(R_N\) cost \(O_W(\log^2 N)\), by enumerating prime powers of primes dividing \(W\). For the other terms bound \(\Lambda(N-j)\le\log N\). The PNT in progressions for this **fixed** \(W\), summed over the reduced classes of \(j\) with \((N-j,W)=1\), bounds the remaining mass divided by \(N\log N\) by
\[
 \prod_{p\mid W,\ p\nmid N}(1-1/(p-1))+o_W(1).
\]
Nonreduced classes with nonzero \(\Lambda(j)\) cost another \(O_W(\log^2 N)\). There are finitely many residues of \(N\bmod W\), so the error is uniform in that residue. At most one odd prime divides a target in these families, so the product is at most twice the same product over all \(p\mid W\). It tends to zero as the cutoff grows, by divergence of the prime reciprocal sum. Taking \(N\to\infty\) first gives \(R_N=o(N\log N)\), hence \(U_N=o(N\log N)\). Now apply both energy identities. This gives leading asymptotics for the individual energies while leaving a difference on the linear scale unresolved.

[P] **What distinguishes actual weights.** On a two-point reflection orbit with nonnegative weights \(a,b\), the contribution to \(R_N\) is \(2ab\); at a fixed point it is \(a^2\). The synthetic choice of one unit from each orbit with weight \(2\kappa\), zero elsewhere, has exact mass \(N\) and \(R_N=0\) on the indicated families with no fixed unit. Its centered vector is reflection-odd on the units and zero elsewhere, so \(E_+=0,\ E_-=\kappa N\). In contrast, genuine \(\Lambda\) has the exact divisor identity \(\sum_{d\mid m}\Lambda(d)=\log m\), by factoring \(m\). Its positive products count precisely pairs of prime powers. In particular the fixed point on \(2^k\) gives \((\log 2)^2\) and the fixed point on \(2p^2\) gives \((\log p)^2\), both higher-power products for the ranges considered.

[P] More generally, a positive product on the nonunits forces both coordinates to be powers of the **same** prime \(p\mid N\): any common divisor of \(j\) and \(N\) divides \(N-j\). For a fixed \(p\) there are at most \(L/\log p\) choices for the first coordinate, so the whole nonunit contribution is at most \(L\sum_{p\mid N}\log p\le L^2\). On units, the operative distinction is the *weighted overlap* of prime-power support with its reflection. The divisor identity determines the weights exactly, but a lower bound for this overlap after removing higher powers is the outstanding two-variable estimate. The observed overlap, the one-point masses, and the fixed points have different logical force.

## 4. Three attempts at a pointwise bound

### 4.1 Short intervals of targets and simultaneous centers

[P] An exact smoothing identity gives a real gain for averages. For \(1\le H\le N/2\), restrict \(j<N\) to odd \(j\) and retain even targets \(N+2t,\ 0\le t<H\). By positivity,
\[
 \sum_{t=0}^{H-1} R_{N+2t}\ \ge\
 \sum_{\substack{j<N\\j\ {\rm odd}}}\Lambda(j)
       \sum_{t=0}^{H-1}\Lambda(N-j+2t).
\]
The inner sum is a difference of two \(\psi\)'s on an interval of length \(2H-1\), less the even prime powers (total \(O(\log N)\)). Under the quoted RH bound, uniformly in \(j\), it is \(2H+O(\sqrt N\log^2(2N))\), using a constant for endpoints below 74. The outer mass is \(N+o(N)\) by PNT. Thus for \(H/(\sqrt N\log^2 N)\to\infty\) the average is at least \((2-o(1))N\). Removing one term of size \(O(N)\) changes the average by \(O(N/H)\). At \(H=1\) the displayed control of the inner sum is vacuous. For the centered \(U_{N+2t}\), the reference set and \(\kappa\) can change with \(t\) as well.

[P] A finite test can give **all other even centers simultaneously** large convolution values for a *synthetic* weight. Work on \(\mathbb Z/M\mathbb Z\), \(M=2^k\ge8\). Independently choose one site in each pair \(\{x,-x\}\) of odd residues. Put \(w=4\) on the chosen sites, zero elsewhere, and \(C(s)=\sum_x w(x)w(s-x)\). Then \(\sum w=M,\ C(0)=0\). For even \(s\ne0\), both sites are odd whenever \(x\) is odd. Unless \(2x=s\), the sites belong to distinct random orbits: they cannot be negatives since \(s\ne0\). Their expected product is 4. At the \(f_s\in\{0,2\}\) odd fixed sites it is 8. Thus \(\mathbf E C(s)=2M+4f_s\). Flipping one of the \(M/4\) orbit choices affects at most four ordered terms by at most 16 each. Bounded differences gives
\[
 \Pr\{|C(s)-\mathbf E C(s)|\ge t\}
 \le 2\exp[-2t^2/(1024M)].
\]
At \(t=64\sqrt{M\log M}\), the union bound over fewer than \(M\) centers is \(<1\). Some choice therefore has \(C(s)=2M+O(\sqrt{M\log M})\) at **every nonzero even shift**, yet an exact hole at zero. This is a cyclic test of transferring neighboring values, with no assertion that the synthetic weights satisfy ERH.

[I] Recovery of one specified target would require, for example, a one-sided bound on the average minus the central value, smaller than the average's margin over the higher-power contribution. Fourier smoothing leaves that discrepancy weighted by \(1-\widehat K\), where \(K\) is the normalized window. The untreated part includes the frequencies at which the window damps single-target information. The simultaneous-center example measures precisely what can be lost even with excellent neighboring values.

### 4.2 Vaughan or Heath-Brown in the reflection basis

[P] Let \(P_\pm=(I\pm r)/2\) on real weights on \(J\). Writing \(h=\sum_i f_i\) by any exact divisor decomposition, the contribution indexed by \(i,j\) is
\[
 \langle P_+ f_i,P_+ f_j\rangle-\langle P_- f_i,P_- f_j\rangle
   =\langle f_i,r f_j\rangle.
\]
This follows by expanding and using \(r^*=r,\ r^2=I\). Discarding cross terms would change the sum. Reflection takes a divisor constraint \(d\mid j\) into \(j\equiv N\bmod d\), so the projection keeps the shifted arithmetic constraint.

[Q] In Vaughan's long-divisor term the report obtains \(\sum_{d>D}\mu(d)\sum_{k>K,\ dk<N}b_k\Lambda(N-dk)\), \(b_k=\sum_{v\mid k,\ v>K}\Lambda(v)\). [Source](../../proof/strong_goldbach_research.md#3-attack-2--divisor-decompositions-and-a-matched-parity-countermodel)

[P] On \(d,k\asymp\sqrt N\), even setting the varying inner weights aside, charging \(\sqrt N\) separate progression errors of order \(\sqrt N\log^2 N\) spends \(N\log^2 N\). Cauchy–Schwarz in \(d\), followed by expansion, requires off-diagonal sums in \(d\) of \(\Lambda(N-dk_1)\Lambda(N-dk_2)\) with the range restrictions on \(k_i,d\). The two forms satisfy \(k_2(N-dk_1)-k_1(N-dk_2)=N(k_2-k_1)\). A further Heath-Brown factorization subdivides \(k\) or \(d\) and keeps the equation between the product and the prime. [I] The missing gain is cancellation or one-sided domination for these **genuine joint weights**, uniform in the target. Merely computing either projected norm separately or summing individual GRH progression errors does not deliver it.

### 4.3 Combining the signed criteria and ERH zero estimates

[P] Positivity alone gives \(U_N\ge\kappa N-2\kappa\psi_{\rm unit}(N)\). By the upper Schoenfeld bound, this yields \(u_N\ge-1-L^2/(4\pi\sqrt N)\) under RH. It approaches the saturation level from below. To reach H3 one needs an improvement at the target above this boundary. The diagonal lower bounds in §3 on the two sparse families are \(O(L^2)\), while a fixed normalized improvement costs order \(\kappa N\). If the only aim is prime positivity one can use the smaller exact sufficient threshold in Theorem 3, but the higher powers then still need to be subtracted.

[Q] H1 evaluates the two major arcs and asks for \(F_N(\mathbb T\setminus A)\ge-0.764480N\). H2 asks for a signed complementary coefficient on growing arcs, with \(-N/3\) a uniform sufficient bound. [Source](../../proof/strong_goldbach_research.md#1-an-explicit-one-sided-minor-arc-criterion)

[P] For each aperture \(A\), \(F_N(A^c)=R_N/e-F_N(A)\). Subtracting two such identities cancels \(R_N\); averaging them with weights of total one leaves exactly one copy of \(R_N/e\). A major-arc comparison can refine a threshold, but it cannot determine this common unknown. The repository's \(1600N^{5/2}L^3\) mean-square allowance for its Farey-model errors accommodates a single error of magnitude \(N\), costing \(N^2\). This error sequence is defined using a different model from H1/H2.

[P] Under ERH the same-sign full-line pair diagnostic at height \(T\) has individual gamma quotient of size \(\asymp T^{-1/2}\) by Stirling; the exponentials from the two numerators cancel that from the denominator. With \(\asymp T\log T\) positive zeta ordinates in \([T,2T]\) by zero counting, the absolute block costs \(\asymp T^{3/2}\log^2 T\). Even at conductor one, setting each real part to \(1/2\), or bounding the number of zeros to its right, gives no signs for the quotient times \(N^{i(\gamma+\gamma')}\). For \(q\mid N\) and conjugate characters the rational-center sum \(\sum_{a\bmod q}^*\chi(a)\bar\chi(a)e(-aN/q)\) equals \(\varphi(q)\). The calculation is a finite-block diagnostic after full-line inversion. It does not replace the truncated arc kernel.

[U] No estimate tested here simultaneously retains the pair phases, gives the required one-sided error at each even target, and is uniform over the relevant conductors and remaining arc terms. The failure of these deductions leaves the implication from ERH to pointwise Goldbach open.

## 5. Proposed Lean micro-lemma, in two declarations

[P] The finite specification and proof below ran with the locally installed Lean 4.16.0 and its matching Mathlib. Both declarations were present. The dependency query returned exactly propext, Classical.choice and Quot.sound for each. This is a local version-specific proof of the two **finite identities**. [U] Project status is **proposed**. There is no strict-check verdict against the attack project's 4.36.0 pin or a registered statement. The second declaration is the literal finite expansion with arbitrary real input \(a\); substituting \(a=\Lambda\) gives (6) before the exponential normalization.

[P] Proof sketch. Subtract the squares term by term. For the second declaration, reflect the reduced residues by an explicit inverse, count them using the totient, then expand both products according to membership in the reduced residues. The assumption \(1<N\) excludes the anomalous totient endpoint \(N=1\).

```lean
import Mathlib

open Finset
open scoped BigOperators

namespace B002

theorem reflection_energy (N : ℕ) (h : ℕ → ℝ) :
    (∑ j ∈ Ioo 0 N, h j * h (N - j)) =
      (∑ j ∈ Ioo 0 N, ((h j + h (N - j)) / 2) ^ 2) -
      (∑ j ∈ Ioo 0 N, ((h j - h (N - j)) / 2) ^ 2) := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem centered_expansion (N : ℕ) (hN : 1 < N) (a : ℕ → ℝ) :
    let κ : ℝ := (N : ℝ) / N.totient
    let h := fun j => a j - (if N.Coprime j then κ else 0)
    (∑ j ∈ Ioo 0 N, a j * a (N - j)) =
      (∑ j ∈ Ioo 0 N, h j * h (N - j)) +
      2 * κ * (∑ j ∈ (Ioo 0 N).filter (Nat.Coprime N), a j) - κ * N := by
  dsimp only
  let S := Ioo 0 N
  let V := S.filter (Nat.Coprime N)
  let κ : ℝ := N / (N.totient : ℝ)
  have symmUnit (j : ℕ) (hj : j ∈ S) :
      N.Coprime (N - j) ↔ N.Coprime j :=
    Nat.coprime_self_sub_right (Finset.mem_Ioo.mp hj).2.le
  have reflected (j : ℕ) (hj : j ∈ V) : N - j ∈ V := by
    obtain ⟨hs, hu⟩ := Finset.mem_filter.mp hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ?_, (symmUnit j hs).2 hu⟩
    obtain ⟨_, _⟩ := Finset.mem_Ioo.mp hs
    constructor <;> omega
  have twice (j : ℕ) (hj : j ∈ V) : N - (N - j) = j := by
    have := (Finset.mem_Ioo.mp (Finset.mem_filter.mp hj).1).2
    omega
  have swap : (∑ j ∈ V, a (N-j)) = ∑ j ∈ V, a j :=
    Finset.sum_nbij' (N - ·) (N - ·) reflected reflected twice twice (fun _ _ => rfl)
  have sets : V = (range N).filter (Nat.Coprime N) := by
    ext j
    simp only [V, S, Finset.mem_filter, Finset.mem_Ioo, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hj⟩, hc⟩
      exact ⟨hj, hc⟩
    · rintro ⟨hj, hc⟩
      refine ⟨⟨?_, hj⟩, hc⟩
      by_contra! hz
      have : j = 0 := by omega
      subst j
      have := (Nat.coprime_zero_right N).mp hc
      omega
  have cardV : V.card = N.totient := sets ▸ (Nat.totient_eq_card_coprime N).symm
  have nonzero : (N.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < N)).ne'
  have norm : (V.card : ℝ) * κ = N := by
    rw [cardV]
    dsimp [κ]
    field_simp
  have expand :
      (∑ j ∈ S, (a j - (if N.Coprime j then κ else 0)) *
        (a (N-j) - (if N.Coprime (N-j) then κ else 0))) =
      (∑ j ∈ S, a j * a (N-j)) -
      (∑ j ∈ V, (κ * a j + κ * a (N-j) - κ^2)) := by
    rw [show V = S.filter (Nat.Coprime N) from rfl, Finset.sum_filter,
        ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [symmUnit j hj]
    by_cases hu : N.Coprime j
    · simp only [if_pos hu]
      ring
    · simp only [if_neg hu, sub_zero]
  change _ = (∑ j ∈ S, _) + 2 * κ * (∑ j ∈ V, a j) - κ * N
  rw [expand, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, swap, Finset.sum_const, nsmul_eq_mul]
  linear_combination -κ * norm

end B002
```

## Reproducing the computations

[P] The Python certificate below runs with the standard library. Its output is the two outward endpoints reported in §1. The scan source that follows it can be compiled with G++ using C++17 and optimization. Its standard output contains all 24,999 rows, including the energy ratio, the independent unsigned convolution and the mixed mass. Both calculations are included here so they survive cleanup of the scratch directory.


```python
"""Exact rational enclosures for the loss with kappa replaced by 2."""
from fractions import Fraction as F
from math import isqrt

def log_interval(x, terms=34):
    # For 1 <= x <= 2, 2 atanh(z) is a positive series with geometric tail.
    z = (x - 1) / (x + 1)
    value = 2 * sum(z**(2*j+1)/(2*j+1) for j in range(terms))
    error = 2*z**(2*terms+1)/((2*terms+1)*(1-z*z))
    return value, value + error

def atan_interval(q, pairs=12):
    z = F(1,q)
    n = 2*pairs
    lower = sum((-1)**j*z**(2*j+1)/(2*j+1) for j in range(n))
    return lower, lower + z**(2*n+1)/(2*n+1)

C = 4*10**18
root = isqrt(C)
assert root*root == C
k = C.bit_length()-1
l2,u2 = log_interval(F(2))
lr,ur = log_interval(F(C,2**k))
lo,hi = k*l2+lr,k*u2+ur
a,b = atan_interval(5)
c,d = atan_interval(239)
pl,pu = 16*a-4*d,16*b-4*c   # Machin identity
loss_lo = lo**2/(4*pu*root) + 2*lo**2/(C*u2) + F('2.85240')*lo/(2*root)
loss_hi = hi**2/(4*pl*root) + 2*hi**2/(C*l2) + F('2.85240')*hi/(2*root)
scale = 10**18
print('outward endpoints / 10^18:', loss_lo*scale//1, -((-loss_hi*scale)//1))
assert loss_hi < F(105,10**9)
```

```cpp
#include <algorithm>
#include <cmath>
#include <cstdio>
#include <vector>

int main() {
    const int limit = 50000;
    std::vector<long double> lambda(limit + 1), h(limit + 1);
    std::vector<std::vector<int>> factors(limit + 1);
    for (int p = 2; p <= limit; ++p) {
        if (!factors[p].empty()) continue;
        for (int j = p; j <= limit; j += p) factors[j].push_back(p);
        for (long long q = p; q <= limit; q *= p) lambda[q] = logl(p);
    }
    puts("N,phi,U,Eplus,Eminus,normalized,energy_ratio,R,psi_unit,HL_ratio_approx");
    const long double twin = 0.66016181584686957393L; // descriptive Hardy-Littlewood benchmark
    for (int n = 4; n <= limit; n += 2) {
        int phi = n;
        long double predicted = twin;
        std::vector<bool> unit(n, true);
        for (int p : factors[n]) {
            phi -= phi / p;
            for (int j = p; j < n; j += p) unit[j] = false;
            if (p > 2) predicted *= 1 + 1.L/(p*(static_cast<long double>(p)-2));
        }
        const long double kappa = static_cast<long double>(n)/phi;
        long double mass=0, r=0, u=0, plus=0, minus=0;
        for (int j=1; j<n; ++j) {
            h[j] = lambda[j] - (unit[j] ? kappa : 0);
            if (unit[j]) mass += lambda[j];
        }
        for (int j=1; j <= n/2; ++j) {
            const int m=n-j, w=(j==m ? 1 : 2);
            const long double a=(h[j]+h[m])/2, b=(h[j]-h[m])/2;
            plus += w*a*a;
            minus += w*b*b;
            u += w*h[j]*h[m];
            r += w*lambda[j]*lambda[m];
        }
        const long double scale=kappa*n;
        if (fabsl(u-(plus-minus))>1e-12L*scale ||
            fabsl(r-(u+2*kappa*mass-scale))>1e-12L*scale) return 1;
        printf("%d,%d,%.13Lf,%.13Lf,%.13Lf,%.13Lf,%.13Lf,%.13Lf,%.13Lf,%.13Lf\n",
               n, phi, u, plus, minus, u/scale, plus/minus, r, mass, predicted-1);
    }
}
```

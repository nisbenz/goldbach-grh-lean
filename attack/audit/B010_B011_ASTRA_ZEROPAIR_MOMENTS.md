# Zero-pair blocks and the single-coefficient moment budget

[Q] Wave 2, 27 November 2026, astra-w2-b011, issues #8 and #7. Tags cover the following paragraph, display or table. [Q] denotes a sourced input or log, [P] a derivation or finite computation here, [I] an interpretation and [U] an unresolved estimate. Only the finite-budget lemma below received a local Lean compilation and axiom audit.

[P] A positive-ordinate **full-line** dyadic block for two primitive characters of conductors \(d,d'\) admits the bound \(O(T\log(2dT)\log(2d'T))\), uniformly in the target. The proof below exploits the beta integral and a local zero count. On a fixed **finite arc**, individual terms at height \(T\) instead decay exponentially. For the exceptional-set model, retaining its two energy bounds improves the single-coefficient power to \(1+1/(2p)\) for the \(p\)-moment and to \(1\) with a logarithm at the endpoint. [U] Both blockers remain open. The deductions supply neither a sufficient signed constant at the target nor control of its minor-arc complement.

## 1. What oscillates on the full line

[Q] Write \(a,b\in[T,2T]\) for positive ordinates, \(h=a+b\), \(r=1/2+ia,\ r'=1/2+ib\). On Dirichlet ERH these real parts apply to all the nontrivial zeros in question. Use ordered pairs, including the diagonal with multiplicities. The finite-block comparison uses \(D=e^{-1}N^{ih}B(r,r')\), where \(B(r,r')=\Gamma(r)\Gamma(r')/\Gamma(r+r')\). The inverse transform at real part one is understood through symmetric or Abel inversion. We use it only on finite blocks. [Source, §2](../../proof/strong_goldbach_research.md#2-attack-1--the-signed-minor-arc-coefficient-and-pairs-of-zeros)

[P] On continuous branches in the positive quadrant the exact phase modulo \(2\pi\) is \(h\log N+\Im(\log\Gamma(r)+\log\Gamma(r')-\log\Gamma(1+ih))\). The shifted Stirling expansion has imaginary part \(t\log t-t+(c-1/2)\pi/2-B_2(c)/(2t)+O(t^{-3})\) at \(c+it\). Thus the phase is
\[
h\log N+a\log a+b\log b-h\log h-\pi/4
 +1/(24a)+1/(24b)+1/(12h)+O(T^{-3}).
\]
The main gradient is \((\log(Na/h),\log(Nb/h))\). Its Hessian has diagonal entries \(1/a-1/h,1/b-1/h\), off-diagonal \(-1/h\), and radial null vector \((a,b)\). The continuous leading phase has no simultaneous stationary point for even \(N\ge4\). Direct integration by parts against Lebesgue measure, or differencing an evenly spaced index, would therefore be an unjustified replacement of the discrete zero measure. The exact modulus follows from reflection,
\[
 |B(r,r')|^2=\frac{\pi\sinh(\pi h)}
 {h\cosh(\pi a)\cosh(\pi b)}.
\]
It gives the usual unweighted zeta triangle sum of order \(T^{3/2}\log^2 T\). The factor \(e^{-1}\) appears in all our numerical full-line values.

### A full-line bound using local zero density

[P] Let \(A,B\) now denote finite multisets in \([T,2T]\), \(T\ge2\), with at most \(L_A,L_B\) points respectively in each interval of length one. For arbitrary individual weights \(|u_a|,|v_b|\le1\),
\[
 \left|\sum_{a,b}u_av_b e^{-1}N^{i(a+b)}
 B(1/2+ia,1/2+ib)\right|\ll T L_A L_B .
 \tag{1}
\]
The constant is absolute. Absorb \(N^{ia},N^{ib}\) into the weights. Euler's exact integral for each beta factor has density \(dx/\sqrt{x(1-x)}\) and phase \(a\log x+b\log(1-x)\). Choose a smooth cutoff equal to one on \([0.30,0.70]\) and supported in \([1/4,3/4]\). It covers every stationary point \(a/(a+b)\in[1/3,2/3]\).

[P] On the complementary piece set \(y=\log(x/(1-x))\). The amplitude becomes \((1-\text{cutoff}(x))/(2\cosh(y/2))\), with integrable derivatives through order two. The phase derivative in \(y\) is \(a-(a+b)x\), of magnitude \(\gg T\) on that support. Its next two derivatives are \(O(T)\). Twice integrating by parts, with vanishing endpoint terms, costs \(O(T^{-2})\) per pair, hence \(O(L_A L_B)\) in total.

[P] On the central piece apply Cauchy–Schwarz in \(x\) to the two exponential sums. For the first factor change variable \(s=\log x\), and for the second use \(s=\log(1-x)\). Both Jacobians and the original density are bounded there. For either sum, on the resulting fixed interval \(J\), use a smooth nonnegative majorant of \(\mathbf1_J\). Expanding the square and integrating gives
\[
 \int_J\Big|\sum_{a\in A}u_a e^{ias}\Big|^2ds
 \ll\sum_{a,a'\in A}(1+|a-a'|)^{-2}\ll \#A\,L_A .
\]
For each \(a\), group the differences into intervals of length one. The sum over bins converges uniformly, including for repeated ordinates. The same bound for \(B\) gives \(O(\sqrt{\#A\,\#B\,L_A L_B})\), hence (1).

[P] For a primitive character of conductor \(d\), the unit-interval count is \(O(\log(2dT))\). For example, use the completed logarithmic derivative in the companion proof at \(s=2+it\). Taking real parts in its Hadamard identity gives a sum of positive \((2-\Re\rho)/|2+it-\rho|^2\), each bounded below by an absolute constant for \(|t-\Im\rho|\le1\). The conductor factor and gamma derivative contribute \(O(\log(2dT))\), the Euler series at 2 is bounded, and the zeta polynomial contributes \(O(1)\). Substituting this local count proves the opening full-line estimate under ERH for the zero-pair model. [Completed-product input](../../proof/weak_goldbach_proof.md)

[I] The smooth argument takes place in the beta integral. Differences of ordinates occur only within each separate squared norm. The original kernel couples the **sum** of the two ordinates and the individual gamma phases. A translation-invariant pair correlation of differences does not determine it. Formula (1) gives \(O_\epsilon(T^{1+\epsilon})\) at fixed conductors and also for polynomially bounded conductors with a fixed degree bound. At \(T\asymp N\) it saves the half-power in the triangle estimate but still costs logarithms. [U] A square-root-size block, a uniform linear bound with the required signed constant, and a bound after combining blocks, characters, centers, model cross terms and the complementary arcs are separate questions. The proof gives no summable tail as \(T\to\infty\).

## 2. The finite arc changes which zeros contribute

[P] For \(U=2\pi Nw\), substituting \(u=2\pi N\beta\) in (4) gives the exact comparison
\[
 K_U=\frac{\Gamma(r)\Gamma(r')N^{ih}}{2\pi}
 \int_{-U}^{U}(1-iu)^{-1-ih}e^{-iu}du,\qquad
 \frac{K_U}{D}=\frac{e\Gamma(1+ih)}{2\pi}
 \int_{-U}^{U}(1-iu)^{-1-ih}e^{-iu}du .
\]
Use the principal branch. The complex ratio depends only on \(h,U\). The inner modulus is \(e^{-h\arctan u}/\sqrt{1+u^2}\), and the phase is \(\arctan u-(h/2)\log(1+u^2)-u\), with derivative \(-u(u+h)/(1+u^2)\). For positive ordinates the large saddle is on the negative side at \(u=-h\). The saddle at zero carries the exponential cost of both gamma factors.

[P] Since \(|\Gamma(1/2+ia)|\le\sqrt{2\pi}\exp(-\pi a/2)\), the actual kernel obeys the explicit bound
\[
 |K_U|\le 2\operatorname{asinh}(U)\exp[-h\arctan(1/U)] .
 \tag{2}
\]
For a positive dyadic block multiply this by the two zero counts and use \(h\ge2T\). At \(U=17/4\) the decay rate is \(\arctan(4/17)\) per unit of \(h\). In H2, \(U=(17/4)(N/C)^{1/16}\), \(C=4\cdot10^{18}\). For \(U\ge1\), \(\arctan(1/U)\ge1/(2U)\). A block \(T\asymp N\) on these arcs therefore has exponential suppression in \(N^{15/16}\), even after polynomial factors. Blocks at \(T\lesssim U\) need other estimates. [I] The analytic difficulty on the **complement** survives this calculation. The local bound on selected major arcs cannot establish H1 or H2 on that complement. [H1 and H2](../../proof/strong_goldbach_research.md)

[P] The following numbers are \(|K_U/D|\) for zeta zeros indexed from one. Widths above \(17/4\) illustrate growth of the rescaled width. They are independent of the \(N=32\) used to tabulate the complex values, and do not represent the H2 widths at that numerical target.

| Zero indices | \(h\) | \(U=4.25\) | 17 | 68 | 272 | 1088 |
|---|---:|---:|---:|---:|---:|---:|
| 1, 1 | 28.269 | .00034800 | .091568 | 1.09551 | 1.00303 | 1.00345 |
| 1, 5 | 47.070 | 3.2773e−6 | .015506 | 1.08074 | .99480 | 1.00077 |
| 5, 10 | 82.709 | 6.2869e−10 | .0011631 | .17522 | 1.03383 | .99736 |
| 25, 32 | 194.256 | 2.5400e−21 | 9.4163e−7 | .0068782 | .91985 | .98867 |

[P] For pair (1,1), \(N=32,U=17/4\), direct integration gives \(K_U=0.000057509+0.000018318i\), against \(D=-0.102736+0.139732i\). For this pair the relative *complex* discrepancy at \(U=1088\) is .00530. The ratios can overshoot one. The scratch output records real and imaginary parts and the complex relative discrepancies for all 20 comparisons. Composite 48- and 80-point Gauss–Legendre rules agree to the tolerance enforced by the script. An additional 55-decimal mpmath quadrature in the original \(\beta\) coordinate at \(N=50\) checks pair (1,5) with \(U=17/4\). The numerical tolerances compare implementations and do not certify rounding enclosures.

[P] Direct integration of **all ordered pairs in each block** gives the following signed magnitudes. Each numerical integral uses the same gamma factors as (4) and the two-character case uses separate ordinate lists. The last row is a conjugate-character pair, taken before multiplying center or character coefficients.

| Characters (modulus.Conrey index) | \(T,N\) | \(U=4.25\) | \(U=17\) | \(U=68\) | Full line |
|---|---:|---:|---:|---:|---:|
| 1.1 × 1.1 | 16,16 | 2.455e−6 | .01082 | .66867 | .62463 |
| 1.1 × 1.1 | 32,32 | 7.184e−9 | .0008161 | .23318 | 1.73889 |
| 1.1 × 1.1 | 64,64 | 1.411e−15 | .00002009 | .06443 | 3.95425 |
| 1.1 × 1.1 | 128,128 | 1.551e−28 | 2.257e−10 | .0006143 | 14.3595 |
| 5.2 × 5.3 | 64,50 | 1.108e−15 | .000009183 | .01613 | 1.41040 |

## 3. Dyadic numerical diagnostic on the full line

[P] FLINT returned the indexed zeta zeros through height 2048, 1,561 positive ordinates. The first is below the first tabulated block. For the four primitive characters 3.2, 4.3, 5.2 and 5.3, sign changes of the real Hardy \(Z_\chi(t)\) on \([8,128]\) produced respectively 63, 69, 73 and 73 candidate ordinates. The meshes \(1/4\) and \(1/8\) gave matching roots within \(10^{-9}\). Brent refinement checked residuals below \(10^{-9}\). [I] The non-zeta samples can miss an even multiplicity or two crossings inside a mesh interval. Their completeness has no certificate. All complex sums use binary64 log-gamma evaluations, cross-checked in modulus against the reflection formula. The conclusions below concern these finite positive-positive blocks.

[P] Write \(V=\sum D,\ A=\sum|D|\), within the half-open block \([T,2T)\). These are the rows with \(N=T\).

| \(T\) | Zeros | \(A\) | \(|V|\) | \(|V|/A\) | \(|V|/\sqrt T\) | \(|V|/N\) |
|---:|---:|---:|---:|---:|---:|---:|
| 16 | 3 | 1.1675 | .6246 | .5350 | .1562 | .03904 |
| 32 | 10 | 9.4540 | 1.7389 | .1839 | .3074 | .05434 |
| 64 | 28 | 52.262 | 3.9542 | .07566 | .4943 | .06179 |
| 128 | 69 | 224.39 | 14.359 | .06399 | 1.269 | .11218 |
| 256 | 167 | 930.40 | 24.791 | .02665 | 1.549 | .09684 |
| 512 | 390 | 3589.8 | 56.103 | .01563 | 2.479 | .10958 |
| 1024 | 893 | 13315.7 | 98.056 | .007364 | 3.064 | .09576 |

[P] At \(T=1024\), taking \(N=1058=2\cdot23^2\) gives \(|V|=95.997\), ratio .007209. At \(N=1922=2\cdot31^2\) these are 24.116 and .001811. At \(N=2048\) they are 8.331 and .0006256. At fixed \(N=8\) the largest block gives 21.035, or \(2.629N\). On the \(T=N\) sequence above the last four \(|V|/N\) lie between .0957 and .1122 while \(|V|/\sqrt T\) increases. [I] The observed decrease of \(|V|/A\) coexists with near-linear sized examples on these heights. Finite data distinguish neither \(T^{1/2+\epsilon}\) nor a uniform \(O(N)\) law. Equation (1) provides the independent near-linear-in-\(T\) upper bound, including when \(T\) and \(N\) vary independently.

[P] Across conductors at \(T=64,\ N=50\), the computations give the following unweighted positive-pair sums.

| Family | Ordinates | Triangle | Signed magnitude | Ratio |
|---|---:|---:|---:|---:|
| 1.1 × 1.1 | 28 × 28 | 52.263 | 3.39594 | .064979 |
| 3.2 × 3.2 | 38 × 38 | 96.388 | 2.82585 | .029318 |
| 4.3 × 4.3 | 42 × 42 | 117.264 | 1.29826 | .011071 |
| 5.2 × 5.2 | 44 × 44 | 129.058 | 2.45634 | .019033 |
| 5.2 × 5.3 | 44 × 44 | 129.143 | 1.41040 | .010921 |

[P] [Chart of the finite-arc ratios against rescaled width](/tmp/astra_w2_b011/kernel_width.png)

### Exact rational-center check

[P] If \(q\mid N\), then \(e(-aN/q)=1\). Multiplying the unit variable by a unit on which the product character is nontrivial proves \(C_q=0\) for every nonprincipal product. For a principal product every summand is one, so \(C_q=\varphi(q)\). Exactly \(\varphi(q)\) of the ordered pairs survive, one conjugate partner per character. The code independently summed the FLINT character exponents on every unit in the cyclotomic polynomial quotient \(\mathbb Z[x]/\Phi_d(x)\) for the unit group exponent \(d\). All 1,366 pairwise evaluations agreed exactly. The table pools every divisor \(q\) of the indicated \(N\), including \(q=1\).

| \(N\) | Character pairs tested | Nonzero | Distinct \(|C_q|\) |
|---:|---:|---:|---|
| 8 | 22 | 8 | 0, 1, 2, 4 |
| 16 | 86 | 16 | 0, 1, 2, 4, 8 |
| 32 | 342 | 32 | 0, 1, 2, 4, 8, 16 |
| 18 | 82 | 18 | 0, 1, 2, 6 |
| 50 | 834 | 50 | 0, 1, 4, 20 |

[I] At these divisors, center summation removes most character pairs but retains the full \(\varphi(q)\) on each survivor. The actual rational-arc expansion also contains the individual expansion coefficients, induced-character corrections and other terms. Treating these diagnostic sums as the entire minor coefficient would discard those terms.

## 4. Optimizing the Fourier moment bound

[Q] All norms on the circle use measure one. In the companion exceptional-set dissection put \(D=S-M,\ G=S+M,\ F=DG,\ E_n=\widehat F(n)\) and \(L=\log N\). With its stated Dirichlet ERH inputs the report gives \(\|D\|_\infty\le20 N^{3/4}L\) **and** \(\|S\|_2^2+\|M\|_2^2\le2NL\). The separate energy bound for \(M\) is essential. This dissection has different arcs from H1/H2. [Companion proof, Lemma 1](../../proof/binary_goldbach_exceptional_proof.md)

[P] Each coefficient has the endpoint estimate
\[
 |E_n|\le\int|S^2-M^2|\le\|S\|_2^2+\|M\|_2^2\le 2NL .
\]
For \(2\le p<\infty\), the companion Bessel estimate and this endpoint give
\[
 \sum_{n\ge1}|E_n|^p\le (2NL)^{p-2}\,1600N^{5/2}L^3
 = 1600\,2^{p-2} N^{p+1/2}L^{p+1}.
 \tag{3}
\]
Thus \(\beta(p)=p+1/2\) and the power obtained by spending the whole moment on one coefficient is \(1+1/(2p)\). Logarithms can be absorbed into \(N^\epsilon\) for fixed \(p\). Direct use of the endpoint is stronger for a specified coefficient. At a threshold \(\delta N\) the moment count still permits \(O_{p,\delta}(\sqrt N L^{p+1})\) exceptions. The endpoint logarithm alone already exceeds any fixed target margin for sufficiently large \(N\).

| [P] \(p\) | Moment power \(\beta(p)\) | Single-term power \(\beta(p)/p\) |
|---:|---:|---:|
| 2 | 5/2 | 5/4 |
| 4 | 9/2 | 9/8 |
| 6 | 13/2 | 13/12 |
| \(p\to\infty\) | — | tends to 1 |

[P] Equivalently, Hausdorff–Young gives \(\|E\|_{\ell^p}\le\|DG\|_{p'}\le\|D\|_r\|G\|_2\) for \(r=2p/(p-2)\), including \(r=\infty\) at \(p=2\). Both \(\|D\|_2,\|G\|_2\le2\sqrt{NL}\). Interpolating \(D\) between 2 and infinity gives power \(1/2+1/(2p)\) for \(\|D\|_r\). For instance \(\int|D|^4\le\|D\|_\infty^2\|D\|_2^2\le1600N^{5/2}L^3\). Its fourth root has exponent \(5/8\), yielding \(9/8\) at \(p=4\). Bounding only \(\|E\|_{\ell^2}\) then using nesting loses this improvement and repeats \(5/4\).

[P] The powers in (3) are sharp for **these norm inputs alone**. Let \(I\) be a circle interval of length \(N^{-1/2}\). Take \(M=0,\ S=N^{3/4}\mathbf1_I e(n_0\alpha/2)\) with \(n_0=N\) even. Then \(\|S\|_2^2=N,\ \|D\|_\infty=N^{3/4}\). Its model error coefficient at \(n_0+k\) has modulus \(N|\operatorname{sinc}(\pi k N^{-1/2})|\), where \(\operatorname{sinc}u=\sin(u)/u\). For \(|k|\le\sqrt N/4\) this is \(\gg N\). There are \(\gg\sqrt N\) positive such indices, and at \(k=0\) its modulus is exactly \(N\). Multiplying \(S\) by \(i\) makes the center coefficient negative. This shows both lower bounds on the allowable powers and the sign ambiguity for the abstract norm class. The test functions are not asserted to arise from primes.

[P] If one literally assumes only \(\|S-M\|_\infty\ll N^{3/4}L\) and \(\int|S|^2\ll NL\), the missing \(\int|M|^2\) changes the answer. On the unit circle \(\|2SD-D^2\|_2\le2\|D\|_\infty\|S\|_2+\|D\|_\infty^2\), allowing power \(3/2\) for every \(\ell^p,\ p\ge2\). Taking \(S=0,\ M=N^{3/4}e(n_0\alpha/2)\) attains \(N^{3/2}\) in a single coefficient. Thus with just those two inequalities the sharp moment power is \(3p/2\). The stronger answer (3) uses an energy bound actually available in the cited proof.

[P] For this specific Hölder deduction, if \(\|D\|_r\ll N^{\delta_r+\epsilon}\) with \(r=2p/(p-2)\), the power of \(\|E\|_{\ell^p}\) is at most \(1/2+\delta_r+\epsilon\), absorbing the logarithm. An exponent \(\delta_r<1/2\) would break one. Equivalently a bound \(\int |D|^r\ll N^{r/2-\eta}\) with fixed \(\eta>0\) suffices for finite \(r\). At \(r=2\), \(\|D\|_2=o(\sqrt{N/L})\) already suffices for \(o(N)\) using the available \(\|G\|_2\). Equality of powers could suffice with adequate constants and logs. [U] A power-saving error norm or an independent one-sided bound at the specified frequency is missing. Such a norm improvement is sufficient for this deduction, not logically necessary for pointwise Goldbach.

## 5. Formal budget lemma and reproducibility

[P] The scratch theorem ranges over every finite index type, real-valued function, and real exponent \(p\ge1\). The one hypothesis on the sum bounds every individual term and the threshold count times \(T^p\) for every real \(T>0\), including equality at the threshold. Here is the complete source compiled with Lean 4.16.0.

~~~lean
import Mathlib

open Finset

theorem momentBudget {ι : Type*} [Fintype ι] (E : ι → ℝ) (p B : ℝ) (hp : 1 ≤ p)
    (hB : ∑ i, |E i| ^ p ≤ B) :
    (∀ i, |E i| ^ p ≤ B) ∧
    (∀ T : ℝ, 0 < T →
      ((univ.filter (fun i => T ≤ |E i|)).card : ℝ) * T ^ p ≤ B) := by
  classical
  have hpos (i : ι) : 0 ≤ |E i| ^ p := Real.rpow_nonneg (abs_nonneg _) _
  constructor
  · intro i
    exact (single_le_sum (fun j _ => hpos j) (mem_univ i)).trans hB
  · intro T hT
    let A := univ.filter (fun i => T ≤ |E i|)
    calc
      (A.card : ℝ) * T ^ p = ∑ _i ∈ A, T ^ p := by simp
      _ ≤ ∑ i ∈ A, |E i| ^ p := sum_le_sum fun i hi =>
        Real.rpow_le_rpow hT.le (mem_filter.mp hi).2 (zero_le_one.trans hp)
      _ ≤ ∑ i, |E i| ^ p :=
        sum_le_sum_of_subset_of_nonneg (subset_univ A) (fun i _ _ => hpos i)
      _ ≤ B := hB

#print axioms momentBudget
~~~

[Q] Local compiler and axiom output follow. A second Lean source imported the emitted object and ascribed the independently written quantified proposition to the compiled theorem. The exact-type check exited successfully. The declaration-name and banned-token scans passed.

~~~text
Lean (version 4.16.0, x86_64-unknown-linux-gnu, commit 128a1e6b0a82, Release)
'momentBudget' depends on axioms: [propext, Classical.choice, Quot.sound]
~~~

[Q] The unmodified strict wrapper was copied to scratch so its required log would also stay in scratch. It called the original vendored checker. Its verdict was **REJECTED (not-a-project-module)** followed by **STRICT VERDICT: REJECTED (exit 1; vendored check-lean.mjs, Apache 2.0)**. That checker accepts only PEqualNP or CheckerSuite project modules under its own Lean root. Its path gate precedes proof inspection. [I] The mathematical budget lemma has a local type and axiom audit. No repository strict acceptance or blocker-level proof is claimed. [Lean source](/tmp/astra_w2_b011/MomentBudget.lean) · [Exact-type test](/tmp/astra_w2_b011/CheckStatement.lean) · [Local log](/tmp/astra_w2_b011/lean.log) · [Strict log](/tmp/astra_w2_b011/strict.log)

[P] Reproduction commands follow. Python 3.14.10 was used. The script writes the row-level results beside itself. The zeta list uses FLINT at 80 bits before conversion to binary64. The nonprincipal experiments use the Conrey character numbers indicated in the tables. Use the embedded script below if the temporary directory has been cleared.

~~~sh
cd /tmp/astra_w2_b011
uv venv --python /usr/bin/python3 venv
uv pip install --python venv/bin/python python-flint==0.9.0 scipy==1.18.1 numpy==2.5.5 sympy==1.14.0 mpmath==1.3.0
OPENBLAS_NUM_THREADS=1 venv/bin/python diagnostics.py
bash compile.sh
~~~

[P] All 177 full-line measurements, 15 finite-arc block measurements, 20 individual arc comparisons, exact center sums and ordinates are available in the scratch directory. [Diagnostic script](/tmp/astra_w2_b011/diagnostics.py) · [Full-line blocks](/tmp/astra_w2_b011/blocks.csv) · [Arc blocks](/tmp/astra_w2_b011/arc_blocks.csv) · [Kernels](/tmp/astra_w2_b011/arcs.csv) · [Centers](/tmp/astra_w2_b011/centers.csv) · [Ordinates](/tmp/astra_w2_b011/zeros.csv)

<details>
<summary>[P] Reproducible numerical source and Lean compilation command</summary>

~~~python
"""Run in a directory with python-flint, scipy, sympy, numpy and mpmath installed."""
import csv
import math
from collections import Counter
from pathlib import Path

import mpmath as mp
import numpy as np
import sympy as sp
from flint import acb, arb, ctx, dirichlet_char
from scipy.optimize import brentq
from scipy.special import loggamma, roots_legendre

HERE = Path(__file__).resolve().parent
ctx.prec = 80


def save(name, rows):
    with (HERE / (name + '.csv')).open('w', newline='') as handle:
        writer = csv.DictWriter(handle, fieldnames=rows[0].keys())
        writer.writeheader()
        writer.writerows(rows)


def dirichlet_roots(q, label, step=0.125):
    char = dirichlet_char(q, label)
    assert char.is_primitive()
    def hardy(t):
        z = char.hardy_z(t)
        assert z.imag.contains(0)
        return float(z.real)
    def scan(h):
        roots = []
        left, vl = 8., hardy(8.)
        for right in np.arange(8.+h, 128.+0.5*h, h):
            vr = hardy(float(right))
            if vl * vr < 0:
                root = brentq(hardy, left, right, xtol=1e-12)
                assert abs(hardy(root)) < 1e-9
                roots.append(root)
            left, vl = right, vr
        return np.array(roots)
    coarse, fine = scan(2*step), scan(step)
    assert len(coarse) == len(fine) and np.max(abs(coarse-fine)) < 1e-9
    return fine


def pair_block(gs, hs, family, t, targets):
    g = gs[(gs >= t) & (gs < 2*t)][:, None]
    h = hs[(hs >= t) & (hs < 2*t)][None, :]
    assert g.size and h.size
    height = g+h
    base = loggamma(.5+1j*g) + loggamma(.5+1j*h) - loggamma(1+1j*height) - 1
    amplitude = np.exp(base.real)
    triangle = amplitude.sum()
    # Independent amplitude from the two gamma reflection identities in log form.
    logcosh = lambda x: np.logaddexp(x, -x)-np.log(2)
    x = np.pi*height
    logsinh = x + np.log1p(-np.exp(-2*x))-np.log(2)
    exact = .5*(np.log(np.pi/height)+logsinh-logcosh(np.pi*g)-logcosh(np.pi*h))-1
    assert np.max(np.abs(exact-base.real)) < 1e-10
    rows = []
    for n in sorted(set(targets)):
        value = np.sum(amplitude*np.exp(1j*(base.imag+height*np.log(n))))
        rows.append(dict(family=family,T=t,N=n,ng=g.size,nh=h.size,real=value.real,
                         imag=value.imag,triangle=triangle,signed=abs(value),
                         ratio=abs(value)/triangle,over_sqrtT=abs(value)/np.sqrt(t),
                         over_T=abs(value)/t,over_N=abs(value)/n))
    return rows


def arc_over_line(g, h, width, order):
    # N^(iH) and the numerator gamma factors cancel in the complex quotient.
    s = 1+1j*(g+h)
    nodes, weights = roots_legendre(order)
    panels = int(np.ceil(2*width))  # panel length at most one
    half = width/panels
    mid = -width + half*(1+2*np.arange(panels))
    u = mid[:,None]+half*nodes[None,:]
    integrand = np.exp(1+loggamma(s)-s*np.log(1-1j*u)-1j*u)
    return half*np.sum(integrand*weights)/(2*np.pi)


def arc_rows(zeros):
    rows = []
    for a,b in [(1,1),(1,5),(5,10),(25,32)]:
        g,h = zeros[a-1],zeros[b-1]
        for width in [4.25,17,68,272,1088]:
            ratio = arc_over_line(g,h,width,48)
            independent = arc_over_line(g,h,width,80)
            assert abs(ratio-independent)<1e-10*max(abs(ratio),1e-50)
            logfull = -1+1j*(g+h)*np.log(32)+loggamma(.5+1j*g)+loggamma(.5+1j*h)-loggamma(1+1j*(g+h))
            full = np.exp(logfull)
            arc = full*ratio
            rows.append(dict(i=a,j=b,H=g+h,N=32,U=width,arc_real=arc.real,
                             arc_imag=arc.imag,full_real=full.real,full_imag=full.imag,
                             ratio_real=ratio.real,ratio_imag=ratio.imag,modratio=abs(ratio),
                             complex_relative_error=abs(ratio-1)))
    # Direct original beta integral at a different target and 55 decimal digits.
    with mp.workdps(55):
        n = 50
        g,h = map(mp.mpf,[float(zeros[0]),float(zeros[4])])
        r, rp = .5+1j*g, .5+1j*h
        w = mp.mpf(17)/(8*mp.pi*n)
        z = lambda b: mp.mpf(1)/n-2j*mp.pi*b
        val = mp.gamma(r)*mp.gamma(rp)*mp.quad(
            lambda b: z(b)**(-r-rp)*mp.exp(-2j*mp.pi*n*b), [-w,0,w])
        full = mp.exp(-1)*n**(r+rp-1)*mp.beta(r,rp)
        assert abs(complex(val/full)-arc_over_line(float(g),float(h),4.25,80)) < 1e-17
    return rows


def arc_blocks(samples):
    rows = []
    cases = [(1,1,1,t,t) for t in [16,32,64,128]] + [(5,2,3,64,50)]
    for q,l,m,t,n in cases:
        gs, hs = (arr[(arr >= t) & (arr < 2*t)] for arr in [samples[q,l],samples[q,m]])
        for width in [4.25,17.,68.]:
            def integrate(order):
                x, w = roots_legendre(order)
                panels = math.ceil(2*width)
                half = width/panels
                u = (-width + half*(1+2*np.arange(panels)[:,None]+x)).ravel()
                weights = half*np.tile(w,panels)*np.exp(-1j*u)/(2*np.pi)
                def factors(arr):
                    r = .5+1j*arr[:,None]
                    return np.exp(loggamma(r) + 1j*arr[:,None]*np.log(n) - r*np.log(1-1j*u))
                return (factors(gs)*weights) @ factors(hs).T
            coarse, fine = integrate(48), integrate(80)
            triangle = np.abs(fine).sum()
            assert np.abs(coarse-fine).sum() < 1e-9*triangle
            total = fine.sum()
            rows.append(dict(q=q,l=l,m=m,T=t,N=n,U=width,signed=abs(total),
                             triangle=triangle,ratio=abs(total)/triangle,
                             real=total.real,imag=total.imag))
    return rows


def centers():
    x = sp.Symbol('x')
    rows = []
    for n in [8,16,32,18,50]:
        for q in sp.divisors(n):
            units = [a for a in range(q) if math.gcd(a,q)==1]
            labels = units if q>1 else [1]
            chars = [dirichlet_char(q,k) for k in labels]
            d = chars[0].group().exponent()
            modulus = sp.Poly(sp.cyclotomic_poly(d,x),x)
            exps = [[int(c.chi_exponent(a)) for a in units] for c in chars]
            for l,ea in zip(labels,exps):
                for m,eb in zip(labels,exps):
                    # q divides N, so the additive twist is exactly unity.
                    hist = Counter((a+b)%d for a,b in zip(ea,eb))
                    rem = sp.Poly.from_dict({(k,):v for k,v in hist.items()},x)%modulus
                    expected = len(units) if (l*m-1)%q==0 else 0
                    assert rem == sp.Poly(expected,x)
                    rows.append(dict(N=n,q=q,chi=l,chip=m,exact_C=expected))
    return rows


def main():
    total = int(arb(2048).zeta_nzeros().unique_fmpz())
    zs = acb.zeta_zeros(1,total)
    assert all(z.real.contains(.5) and float(z.imag.rad())<1e-12 for z in zs)
    zeros = np.array([float(z.imag) for z in zs])
    samples = {(1,1): zeros}
    for q,k in [(3,2),(4,3),(5,2),(5,3)]:
        samples[q,k] = dirichlet_roots(q,k)
    save('zeros',[dict(q=q,conrey=k,gamma=t) for (q,k),arr in samples.items() for t in arr])
    blocks = []
    for a,b in [((1,1),(1,1)),((3,2),(3,2)),((4,3),(4,3)),((5,2),(5,2)),((5,2),(5,3))]:
        heights = [16,32,64,128,256,512,1024] if a==(1,1) else [16,32,64]
        for t in heights:
            prime = int(sp.nextprime(math.sqrt(t/2)))
            targets = [8,32,50,128,512,1024,2048,1922,t,2*prime**2]
            blocks.extend(pair_block(samples[a],samples[b],f'{a[0]}.{a[1]}x{b[0]}.{b[1]}',t,targets))
    save('blocks',blocks)
    save('arcs',arc_rows(zeros))
    save('arc_blocks',arc_blocks(samples))
    save('centers',centers())
    print('Completed',len(zeros),'zeta zeros;',len(blocks),'block/target measurements.')

if __name__=='__main__':
    main()
~~~

~~~sh
#!/usr/bin/env bash
set -eu
cd /tmp/astra_w2_b011
packages=/home/nisbenz/.t3/projects/weak-goldbach/lean/.lake/packages
export LEAN_PATH="$(find -L "$packages" -mindepth 4 -maxdepth 4 -type d -path '*/.lake/build/lib' | paste -sd :)"
lean +leanprover/lean4:v4.16.0 --version
lean +leanprover/lean4:v4.16.0 -o MomentBudget.olean MomentBudget.lean
~~~

</details>

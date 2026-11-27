# B-003 / B-012 · Dispersion and the Liouville projection for shifted primes

[P] The five negative Wave 1 off-diagonals reproduce. All nine selected highly composite or primorial multiples give **positive** off-diagonals. On 288 other even targets, the two-form Hardy–Littlewood predictor gets the sign right 273 times. At 30030 the genuine *uncentered* signed mass equals its entire unsigned mass, just as for the plus model on that box. Finite-target separation depends on which target and which statistic one chooses.

[P] A negative off-diagonal has magnitude at most the diagonal, which is \(O(N\log^2 N)\) on these boxes. Thus a negative term of order \(N^{3/2}\) is impossible. [U] The hard direction is to bound positive excursions for each even target. No such uniform upper estimate, no \(o(N)\) estimate for the genuine projection, and no pointwise Goldbach conclusion have been established here, including under named Dirichlet ERH.

[Q] Tags throughout denote a sourced assertion [Q], a displayed derivation or executed finite computation [P], an interpretation [I], and a conjectural, conditional, or unresolved assertion [U]. Numerical tables give finite floating-point measurements. Mathematical derivations below have no repository strict-check verdict. [Wave 1](B012_BILINEAR_PARITY_ATTACK.md) · [B-003 sieve analysis](B003_PARITY_ANALYSIS.md)

## 1. The box and two exact identities

[Q] Put \(h=\lfloor\sqrt{N-1}\rfloor\), \(I=J=(\lfloor h/2\rfloor,h]\cap\mathbb Z\), \(K=|J|\), and \(c_d=d/\varphi(d)\). A star on the row sum restricts to \((d,N)=1\). All columns \(k\in J\) are retained, including nonunits; \(dk<N\) throughout. The literal coefficient is \(A_{dk}=\Lambda(N-dk)\), including higher prime powers. The synthetic coefficients are \(a^\pm_m=\mathfrak S(N)\mathbf1_{(m,N)=1} f(m)(1\pm\lambda(m))\), with \(f(m)=\prod_{p\mid m,\ p>2}(p-1)/(p-2)\) and \(\lambda=(-1)^\Omega\). [Box definition](../../proof/strong_goldbach_erh_attack.md#replacing-d_2-by-primes) · [Normalization](B012_BILINEAR_PARITY_ATTACK.md)

[P] Define \(X_d(k)=\mu(d)(A_{dk}-c_d)\), \(Y(k)=\sum_d^* X_d(k)\), \(G=\sum_kY(k)^2\), \(D=\sum_{d,k}^*X_d(k)^2\), \(O=G-D\), \(C=\sum_d^*\mu(d)c_d\), and \(V=\sum_k\lambda(k)Y(k)\). Here \(O\) counts ordered distinct rows. Since \(G\ge0\),
\[
 O\ge-D,\qquad |V|^2\le K(D+O),\qquad D\ll N\log^2(2N).
\]
For the last inequality use \(\Lambda\le\log N\) and \(c_d\le\zeta(2)\prod_{p\mid d}(1+1/p)\le\zeta(2)\sum_{j\le d}1/j\). In particular \(\max(-O,0)=o(N^{3/2}/\log^A N)\) for every fixed \(A\). On a box where \(O\le0\), the same identities give \(|V|\ll N^{3/4}\log N\). This is a conditional size explanation for negative boxes, with no sign assumption on other targets.

[P] Let \(r(m)\) count the factorizations \(m=dk\) in this box with \((d,N)=1\) and squarefree \(d\). Complete multiplicativity and \(\mu(d)=\lambda(d)\) on these rows give the exact genuine projection
\[
 V=\sum_{m<N}r(m)\lambda(m)\Lambda(N-m)-C\sum_{k\in J}\lambda(k).
\]
It is one bilinear sum, with signed coefficient \(\lambda(k)\). For the two models its raw part is exactly \(\pm\sum_m r(m)a_m^\pm\). Genuine shifted primes can occur on either Liouville sign. At \(N=2^{17}\) their raw signed mass is 284.39 out of 16807.12, then centering subtracts 34.64. The model projections are +16649.63 and −16676.02; the genuine projection is +249.75. This is concrete cancellation in the raw mass, before subtraction of the center.

[Q] On \(N=2^t\), Wave 1 proves \(|V_\pm|\gg N\) and \(O_\pm\gg N^{3/2}\) by PNT, odd squarefree-row density, and \(G\ge V^2/K\). Under PNT each sign occurs on a positive fraction of odd columns and the center is \(o(N)\). The model diagonal is \(O_\epsilon(N^{1+\epsilon})\). [P] A genuine \(|V|=o(N)\) on those targets separates both signs there; a genuine one-sided \(O\le o(N^{3/2}/\log^2 N)\) does as well. Either bound uniform in all even targets would in particular apply there. This lower bound for the models was proved on powers of two. It gives no two-model lower bound on an arbitrary finite box. [Wave 1, §3](B012_BILINEAR_PARITY_ATTACK.md#3-why-the-models-have-a-large-off-diagonal)

## 2. Deriving a numerical covariance prediction

[P] Fix distinct coprime-to-\(N\) rows \(d,e\). For each prime \(p\) count the forbidden column classes
\[
 \nu_p=\#\{t\bmod p:(N-dt)(N-et)=0\bmod p\}.
\]
If \(p\mid(d,e)\) both forms are nonzero constants and \(\nu_p=0\). If exactly one slope is divisible by \(p\), the other form has one root. When both slopes are units, the relation \(e(N-dk)-d(N-ek)=N(e-d)\) shows the roots coincide precisely for \(p\mid N(e-d)\); otherwise they are distinct. In particular \(\nu_2=1\). This count uses no condition \((d,e)=1\).

[U] The two-form Hardy–Littlewood prime-tuple heuristic for the average of the *product* of Mangoldt weights is \(H_N(d,e)=\prod_p(1-\nu_p/p)/(1-1/p)^2\). Single-form factors give \(c_d,c_e\). Replacing the joint and two single averages by these densities predicts
\[
 O_{\rm HL}=K\sum_{d\ne e}^{*}\mu(d)\mu(e)\big(H_N(d,e)-c_dc_e\big).
\]
The intervals and coefficients vary together and the interval has only \(K\asymp\sqrt N\) integers. A conjecture about two **fixed** forms on long intervals does not justify the summed error here. [P] With \(\delta_d=\sum_k\Lambda(N-dk)-Kc_d\) and \(\epsilon_{de}=\sum_k\Lambda(N-dk)\Lambda(N-ek)-KH_N(d,e)\), the discrepancy is exactly the ordered signed sum of \(\epsilon_{de}-c_e\delta_d-c_d\delta_e\). Control of that whole expression would be needed for a quantitative transfer.

[P] The infinite local product itself is elementary to evaluate. Write \(C_2=\prod_{p>2}(1-(p-1)^{-2})\), \(g=(d,e)\), \(u=|d-e|\), and \(r_n=n/\varphi(n)\). Then
\[
 H_N(d,e)=2C_2\,
 \frac{f(N)f(d)f(e)f(u)\,r_g}{f(g)^2 f((N,u))}.
\]
For odd \(p\), changing two roots to one multiplies the generic factor by \((p-1)/(p-2)\); changing one root to zero costs a further \(p/(p-1)\). The exceptions lie in the union of the prime divisors of \(N,d,e,u\). A prime dividing both slopes also divides \(u\) and occurs three times in the numerator; a prime dividing both \(N,u\) occurs twice. These are the only overcounts. The computation enumerates roots independently on selected row pairs for each target. It truncates only the generic product at \(T=2^{20}\). Its absolute omitted log is at most \(\sum_{j>T}1/[j(j-2)]<1/(T-2)\) from \(-\log(1-x)\le x/(1-x)\). The finite product overestimates the limiting value. The resulting absolute error in the **predictor**, apart from roundoff, is bounded by \(K\sum_{d\ne e}^*|\mu(d)\mu(e)|H_{N,T}(d,e)/(T-2)\). This is below 0.70% of \(|O_{\rm HL}|\) at every measured target. The heuristic error for the primes is separate.

[P] The primes dividing \(N\) isolate an interpretable part of the prediction. A single row's conditional local density on unit columns at these primes is \(r_Nc_d\); it is zero on the other columns in the residue model. Their common unit indicator has modeled mean \(1/r_N\). The corresponding contribution to the predicted ordered covariance is
\[
 O_{N\text{-primes}}=K(r_N-1)\left(C^2-\sum_d^*\mu(d)^2c_d^2\right).
\]
Indeed this is the part from \(r_Nc_dc_e-c_dc_e\); the rest is the signed sum of \(H_N(d,e)-r_Nc_dc_e\). The analogous elementary projection baseline is \(V_{N\text{-primes}}=C(r_N\sum_{(k,N)=1}\lambda(k)-\sum_k\lambda(k))\), with sums over \(J\). It models the shared unit restriction only. The genuine calculation includes exceptional primes and their powers, and keeps the remaining congruence and Liouville correlations.

[P] At \(2^{17}\), \(C=4.95\); the common-prime covariance component is −17622, the full prediction −35039, and the observed value −64357. At \(510510\), \(C=-49.57\); the same three numbers are +3880052, +3855044, and +4051562. The projection baseline is +12536.85 there versus +12699.04 observed. The covariance component alone gets the sign right on 270/288 sampled targets, versus 273/288 for the full product. [I] Signed rows can cancel the shared-density contribution or reinforce it. This accounts for much of the observed change of sign. The two-form heuristic by itself specifies no Liouville-twisted prime asymptotic.

## 3. The measurements and exponent test

[P] The 315 distinct targets comprise 27 structured or reference targets and a separate panel of 48 even targets drawn uniformly without replacement from each of the six octaves \([2^i,2^{i+1})\), \(14\le i\le19\), using seed 20261127. The structured set includes every \(2^{14},\ldots,2^{20}\), seven twice-prime-squares, six doublings of 27720, three primorial multiples, all five Wave 1 targets, and 1000000. The upper endpoint 1048576 includes the expressly requested \(2^{20}\). Primality, prime powers, Möbius, Liouville and row membership come from integer sieving. Both synthetic signs use the same product cutoff. The program also calculates the off-diagonal directly by summing the measured ordered row covariances and checks both model projection identities.

[P] Representative rows, with natural logarithms and nearest-unit rounding for the off-diagonals. All 315 full-precision rows are in the CSV. Positive \(O\) appears already at \(2\cdot97^2\); the local predictor misses that sign.

| Even target | Measured \(O\) | Predicted \(O_{\rm HL}\) | Genuine \(V\) | Plus \(V\) | Minus \(V\) |
|---:|---:|---:|---:|---:|---:|
| 16384 | −4330 | −4457 | 123.56 | 2036.24 | −2046.14 |
| 18818 | +2964 | −3915 | 369.16 | 2320.32 | −2343.59 |
| 27720 | +65956 | +66262 | 1219.02 | 2222.74 | +75.63 |
| 30030 | +111919 | +99787 | 1544.94 | 2955.65 | −51.41 |
| 126002 | −9799 | −31947 | 755.43 | 15563.49 | −15606.02 |
| 131072 | −64357 | −35039 | 249.75 | 16649.63 | −16676.02 |
| 510510 | +4051562 | +3855044 | 12699.04 | 34346.93 | −9980.86 |
| 887040 | +2562447 | +2756083 | 7037.69 | 53402.53 | −37865.76 |
| 982802 | −317553 | −227526 | 429.80 | 120215.18 | −120215.13 |
| 1000000 | −335475 | −265651 | −3123.47 | 99130.04 | −99779.06 |
| 1048576 | −122903 | −234183 | 827.29 | 130241.23 | −130151.56 |

[P] At 30030 the unit rows and unit columns in 87 through 173 are primes: 30030 contains every prime through 13 and \(17^2>173\). Enumeration also shows zero genuine mass on nonunit columns. All positive-mass products consequently have \(\lambda(dk)=+1\). The genuine raw signed and unsigned masses both equal 1596.35, while the minus model has zero raw mass. Finite cancellation against both synthetic signs therefore fails on this target.

[P] The individual-target exponent below is the unweighted OLS slope of \(\log |V|\) on \(\log N\). The final column uses Pearson correlation of the measured and predicted \(O/N^{3/2}\). The three structured families are distinct; the full structured set also contains other reference targets.

| Targets | Count | Negative \(O\) | Predicted sign correct | Fitted exponent | \(R^2\) for exponent | Covariance correlation |
|---|---:|---:|---:|---:|---:|---:|
| Powers of two | 7 | 7 | 7 | 0.629 | 0.695 | 0.840 |
| Twice prime squares | 7 | 6 | 6 | −0.082 | 0.028 | −0.538 |
| Highly composite or primorial multiples | 9 | 0 | 9 | 0.618 | 0.879 | 0.989 |
| All structured | 27 | 17 | 26 | 0.523 | 0.220 | 0.992 |
| Separate stratified sample | 288 | 225 | 273 | 0.605 | 0.316 | 0.925 |

[P] Across the six sampled octaves, median \(|V|/N\) falls from 0.003193 to 0.001046; the medians of \(|V|\) are 74.54, 167.16, 287.28, 294.96, 519.22 and 761.25. Regressing those medians on the six median targets in log coordinates gives slope 0.622. Median signed \(O/N^{3/2}\) changes from −0.000841 to −0.000306. Among positive observations only, the first and last octave medians are +0.001049 and +0.000241 (13 and 5 targets respectively). [I] The sample supports a sublinear descriptive fit for the projection. The prime-square fit and the small number of positive observations in the last octave show why extrapolation is fragile. [U] A uniform exponent, an asymptotic little-o on the positive side, and any effective threshold remain undetermined. [Plot](/tmp/astra_w2_b003/dispersion.png) · [Data](/tmp/astra_w2_b003/results.csv)

## 4. Which bound would reach Goldbach?

[P] **Projection versus a Vaughan box.** For a fixed column vector \(b\), the centered term is \(T_b=\sum_k b_kY(k)\). A bound on \(V\) controls only \(b=\lambda\) and its scalar multiples. The orthogonal component of the actual Vaughan coefficient can carry the entire sum even when \(V=0\). By contrast \(|T_b|^2\le\|b\|_2^2(D+O)\). On a balanced rectangular box, \(|b_k|\le L=\log N\) gives \(\|b\|_2^2\ll\sqrt N L^2\). Hence the one-sided bound \(O\le o(N^{3/2}/L^2)\) implies \(T_b=o(N)\) on that box, uniformly if the input is uniform. The stronger sign bound \(O\le0\) would give \(|T_b|\ll N^{3/4} L^2\) there. The positive finite examples disprove an all-target nonpositive sign assertion with onset at the start of this scan. They do not decide an eventual upper estimate.

[P] **The rough-set gap can be localized exactly.** For any input array \(A(m)\) replace it by \(A(m)\mathbf1_{m\text{ composite}}\). Every \(V\), \(G\), \(D\), and \(O\) on every box with \(d,k>1\) is identical. The modified array has zero left-prime mass. Even exact knowledge of every such statistic would leave the prime positions unobserved for general inputs. On the cube-root-rough subset, each observed product \(dk\) has exactly two prime factors and \(\lambda(dk)=+1\), so \(B=U\) identically there. For genuine weights on all rough integers the identity is \(P=(S-B)/2\); a two-prime witness requires \(S-B>2E\), where \(E\) is the mass of left rough primes with reflected higher powers. The erasure argument identifies the information missing from a box-to-rough-mass deduction; it makes no independence assertion about genuine primes or ERH.

[Q/P] **Direct convolution.** Write \(R(N)=\sum_{1\le m<N}\Lambda(m)\Lambda(N-m)\), with \(U,V_0\) Vaughan cutoffs (the subscript distinguishes \(V_0\) from the measured projection). With all variables positive and integer, the exact four terms from Vaughan's identity are
\[
\begin{aligned}
 R(N)={}&\sum_{d\le U}\mu(d)\sum_{dk<N}\log k\;\Lambda(N-dk) \\
 &-\sum_{r\le UV_0}\gamma(r)\sum_{rj<N}\Lambda(N-rj),
 \qquad \gamma(r)=\sum_{dv=r,\ d\le U,\ v\le V_0}\mu(d)\Lambda(v) \\
 &+\sum_{m\le V_0,\ m<N}\Lambda(m)\Lambda(N-m) \\
 &+\sum_{d>U}\mu(d)\sum_{k>V_0,\ dk<N} b_k\Lambda(N-dk),
 \qquad b_k=\sum_{v\mid k,\ v>V_0}\Lambda(v)\le\log k .
\end{aligned}
\]
The coefficient definitions at the right specify the preceding sums. This follows from \(\log=1*\Lambda\) and \(\mu*1=\mathbf1_{n=1}\). The prime-erasure test leaves the last term intact and changes information in the other terms. [Vaughan identity in the repository](../../proof/strong_goldbach_research.md#3-attack-2--divisor-decompositions-and-a-matched-parity-countermodel)

[P] The residual obligations in this exact decomposition are as follows.

1. **[P] First and second Type I terms.** Track the \(d\le U\) log-weighted progression and the free progression for \(r\le UV_0\) with its signed \(\gamma(r)\). For reduced classes their continuous density per free variable is \(r/\varphi(r)\) (or \(d/\varphi(d)\)). Partial summation handles the log with its endpoint. Under named Dirichlet ERH the individual progression error is \(O(\sqrt N\log^2(2Nq))\) for moduli in this range. Summing allowances through \(Q\asymp\sqrt N\) already spends the linear scale before coefficient and logarithmic losses. The second Type I range can be as long as \(UV_0\), even with both individual cutoffs short. The small term costs at most \(V_0 L^2\).
2. **[P] Remaining Type II region.** The entire region is \(d>U,\ k>V_0,\ dk<N\), including unbalanced rectangles, smaller products, and rectangles cut by the hyperbola. Bounds for full balanced rectangles alone give no bound for every clipped subregion by monotonicity: the coefficients are signed. One needs uniform subinterval, smoothly partitioned or appropriately truncated estimates and an error budget for the decomposition. On an unbalanced box of column length \(K'\), the same Cauchy step allows total quadratic form \(o(N^2/(K'L^2))\) for a single \(o(N)\) target error. Summing growingly many boxes requires control of the aggregate errors, e.g. a saving that absorbs their number.
3. **[P] Nonunits and centers.** Rows with \((d,N)>1\) were omitted in the measurement; likewise nonreduced Type I moduli must be handled. Whenever a common prime \(p\mid N,d\) and \(\Lambda(N-dk)\ne0\), the reflected value is a power of \(p\). Only \(O(\omega(N)L)\) such reflected values occur, and divisor multiplicities in these fixed-depth decompositions are \(O_\epsilon(N^\epsilon)\), so these terms can be bounded with logarithmic factors. A centered rectangle also splits off \((\sum_d^*\mu(d)c_d)(\sum_k b_k)\), or the corresponding clipped expression. For weighted columns this subtraction is algebraic; a main term must be established after recombining all contributions.
4. **[U] Pointwise main term or a sufficient lower bound.** The conjectural main term for the full convolution is \(N\mathfrak S(N)\) with \(\mathfrak S(N)=2C_2 f(N)\ge2C_2>0\). Neither the local predictor for the off-diagonal nor a centered Type II estimate evaluates the combined progression and center terms to this value. A sufficient alternative is a pointwise lower bound exceeding the mass with at least one proper prime power. [P] That mass is at most \(2\sqrt N L^2\): for a base \(p\le\sqrt N\) the total weights of its powers up to \(N\) are at most \(L\), and the reflected factor is at most \(L\). A uniform positive multiple of \(N\) for \(R(N)\) would therefore force two primes for sufficiently large even \(N\). It would also give rough left primes after deleting left primes \(\le N^{1/3}\) at cost \(O(N^{1/3}L^2)\) and nonunits (a prime on the left dividing \(N\) yields at most \(\omega(N)L^2\)). A quantitative all-even result would additionally need its finite range bridged.

[I] Thus the direct convolution bypasses the rough identity *if the complete convolution estimate is proved*. Even the proposed one-sided bound on **all balanced** Vaughan boxes, with the genuine coefficients, is insufficient by this decomposition alone. The projection is a weaker diagnostic still.

## 5. Scope of analytic inputs

[Q/P] Dirichlet ERH gives estimates for a single prime progression in the reflected variable. Even discarding the second signed coefficient would cost \(\asymp\sqrt N\) separate error allowances on balanced rows. Keeping \(\lambda(k)\) introduces a varying multiplicative weight that the single progression formula cannot remove by endpoint evaluation. The identity in §1 rewrites it as a shifted Liouville–prime correlation with an additional divisor-count weight. Replacing its weight by an average would require a new error estimate. Wave 1’s parity example shows why sharper estimates restricted to matched linear divisor tests alone cannot give the separating conclusion. [Dirichlet ERH input and balanced dispersion](../../proof/strong_goldbach_erh_attack.md#replacing-d_2-by-primes)

[Q/I] Matomäki–Radziwiłł short-interval cancellation concerns multiplicative-function averages for typical intervals; averaged Chowla-type results also average over shifts. Our target fixes \(N\) and weights \(k\) by both the signed divisor row sum and the reflected Mangoldt values. No transfer controlling the exceptional intervals, growing slopes and prime weight on each chosen target is provided by those statements. Vaughan and Heath-Brown identities can resolve \(\Lambda\) into divisor convolutions, but retain the reflected condition and require additional bounds for their signed sums. Neither an identity nor the local covariance formula proves cancellation. Unconditional PNT for \(\lambda\) suffices to make the **separable center** \(o(N)\) on this box since \(\sum_{d\le h}c_d\ll h\) and \(\sum_{k\in J}\lambda(k)=o(h)\); it leaves the raw term in §1. [Short intervals](https://arxiv.org/abs/1501.04585) · [Averaged Chowla](https://arxiv.org/abs/1503.05121) · [Wave 1 input audit](B012_BILINEAR_PARITY_ATTACK.md#5-estimates-tested-against-the-fixed-target)

[U] The target-uniform genuine \(o(N)\) projection and signed upper dispersion estimate are unresolved by these inputs. This is a limitation on the deductions presented here. There is no proof of nonimplication from ERH.

## 6. Local Lean compilation

[P] The two Wave 1 rough-set theorem headers and the definition of the B-004 proposition agree with their source proposals. The scratch file proves a theorem of the dyadic proposition as well as declaring the proposition. The v4.16.0 Mathlib snapshot lacks the later arithmetic Liouville function. The file defines it transparently as an integer-valued arithmetic function, zero at 0 and \((-1)^{\Omega(m)}\) at positive inputs, under the name `ArithmeticFunction.liouville`. This portability decision matters when moving the proof to v4.36.0. The support cutoff stays real. The proof uses the lower bound for the product of the prime factors supplied by the smallest prime factor. The dyadic proof includes \(h=0\) and works in \(\mathbb Z\) for the final subtraction.

[P] The exact command below exited 0 with the complete output shown. An independent scan found all three theorem declarations and no banned tokens; the B-012 theorem headers match literally and the B-004 proposition matches modulo whitespace. [Lean file](/tmp/astra_w2_b003/Wave2Lemmas.lean) · [Captured output](/tmp/astra_w2_b003/build.log) · [Wave 1 rough-set proposals](B012_BILINEAR_PARITY_ATTACK.md#6-proposed-lean-4-micro-lemma) · [Wave 1 dyadic proposition](B004_B014_GWX_RATIOS_ATTACK.md#4-proposed-lean-micro-lemma-and-issue-disposition)

```sh
cd lean && lake env lean /tmp/astra_w2_b003/Wave2Lemmas.lean
```

```text
'GoldbachAttack.weighted_prime_mass_cuberough' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachAttack.exists_positive_prime_of_cuberough_strict' depends on axioms: [propext, Classical.choice, Quot.sound]
'b004_dyadic_projector' depends on axioms: [propext, Classical.choice, Quot.sound]
```

[U] All three remain **local v4.16.0 compiled proposals pending v4.36.0 strict checking**. The analytic blockers B-003 and B-012 remain open.

## Reproduction

[P] The measurement script uses Python and NumPy only; the optional plot uses Matplotlib. In this checkout the existing scratch interpreter below supplies NumPy 2.5.5 and Matplotlib 3.11.2. The script checks both signed model projections, the genuine row-pair sum, individual local factors, and the five Wave 1 values. The appendices preserve the measurement and Lean sources if scratch storage is cleared. [Measurement](/tmp/astra_w2_b003/measure.py) · [Full numerical report](/tmp/astra_w2_b003/results.txt) · [Plot script](/tmp/astra_w2_b003/plot.py)

```sh
OPENBLAS_NUM_THREADS=1 /tmp/astra_b004/venv/bin/python /tmp/astra_w2_b003/measure.py > /tmp/astra_w2_b003/results.txt
/tmp/astra_b004/venv/bin/python /tmp/astra_w2_b003/plot.py
```

<details><summary>Measurement source</summary>

```python
"""Wave 2. Python 3 + NumPy. Output CSV and text beside this file."""
import csv
import math
import random
from pathlib import Path
import numpy as np

OUT = Path(__file__).resolve().parent
T = 2**20
powers = [2**i for i in range(14, 21)]
squares = [2*p*p for p in (97, 137, 191, 251, 353, 499, 701)]
multiples = [27720*2**i for i in range(6)] + [30030, 510510, 2*30030*13]
wave1 = [100000, 126002, 131072, 200000, 500000]
special = sorted(set(powers+squares+multiples+wave1+[1000000]))
rng = random.Random(20261127)
sample = [2*n for i in range(14, 20) for n in
          rng.sample(range(2**(i-1), 2**i), 48)]
target = sorted(set(special+sample))

prime = np.ones(T+1, dtype=bool)
prime[:2] = False
for p in range(2, math.isqrt(T)+1):
    if prime[p]:
        prime[p*p::p] = False
primes = np.flatnonzero(prime)
mang = np.zeros(T+1)
f = np.ones(T+1)
ratio = np.ones(T+1)
lam = np.ones(T+1, dtype=np.int8)
mu = np.ones(T+1, dtype=np.int8)
for p in map(int, primes):
    ratio[p::p] *= p/(p-1)
    if p > 2:
        f[p::p] *= (p-1)/(p-2)
    if p*p <= T:
        mu[p*p::p*p] = 0
    mu[p::p] *= -1
    q = p
    while q <= T:
        mang[q] = math.log(p)
        lam[q::q] *= -1
        q *= p
podd = primes[1:].astype(float)
constant = 2*math.exp(math.fsum(np.log1p(-1/(podd-1)**2)))
# The omitted log factors have total magnitude <= 1/(T-2).
def analyze(n):
    h = math.isqrt(n-1)
    k = np.arange(h//2+1, h+1)
    d = k[(np.gcd(k,n)==1) & (mu[k]!=0)]
    product = d[:,None]*k
    c = ratio[d]
    def statistics(raw):
        x = mu[d,None]*(raw-c[:,None])
        y = x.sum(axis=0)
        g = y@y
        diag = (x*x).sum()
        off = g-diag
        projection = lam[k]@y
        assert projection**2 <= k.size*g + 1e-5
        a = x[:,0]
        assert math.isclose(2*sum(a[j]*sum(a[:j]) for j in range(len(a))),
                            y[0]**2-a@a, rel_tol=1e-10,abs_tol=1e-7)
        return diag,off,projection,g
    raw = mang[n-product]
    diag,off,v,g = statistics(raw)
    base = constant*f[n]*f[product]*(np.gcd(k,n)==1)
    pp = statistics(base*(1+lam[product]))
    mm = statistics(base*(1-lam[product]))
    i,j = np.triu_indices(len(d),1)
    a,b = d[i],d[j]
    common = np.gcd(a,b)
    diff = b-a
    pair = (constant*f[n]*f[a]*f[b]*f[diff]*ratio[common]/
            (f[common]**2*f[np.gcd(n,diff)]))
    for t in set((0,len(i)//2,len(i)-1)):
        aa,bb = int(a[t]),int(b[t])
        # Independent local check by enumerating k mod small primes and
        # multiplying exceptional factors over all prime divisors.
        corr = 1.
        for l in map(int,primes[primes<=h]):
            if (n*aa*bb*(bb-aa))%l:
                continue
            if l<=31:
                roots = sum(((n-aa*r)*(n-bb*r))%l==0 for r in range(l))
            else:
                roots = len({n*pow(s,-1,l)%l for s in (aa,bb) if s%l})
            if l==2:
                assert roots==1
            else:
                corr *= (l-roots)/(l-2)
        # Large factors of N beyond h affect both forms too.
        rem=n
        for l in map(int,primes[primes<=h]):
            while rem%l==0:
                rem//=l
        if rem>h and rem>2:
            corr *= (rem-1)/(rem-2)
        assert math.isclose(constant*corr,pair[t],rel_tol=2e-13)
    hl = 2*len(k)*np.sum(mu[a]*mu[b]*(pair-c[i]*c[j]))
    trunc_err = 2*len(k)*np.sum(pair)/(T-2)
    joint = raw@raw.T
    # Direct measured ordered covariance, independent of G-D.
    rowmean = raw.mean(axis=1)
    direct = 2*np.sum(mu[a]*mu[b]*(joint[i,j]-len(k)*
                      (c[j]*rowmean[i]+c[i]*rowmean[j]-c[i]*c[j])))
    assert math.isclose(off,direct,rel_tol=1e-9,abs_tol=1e-6)
    row_center = float(mu[d]@c)
    cent = row_center*int(lam[k].sum())
    unit = np.gcd(k,n)==1
    common_cov = len(k)*(ratio[n]-1)*(row_center**2-c@c)
    common_proj = row_center*(ratio[n]*int(lam[k[unit]].sum())-int(lam[k].sum()))
    assert math.isclose(pp[2], (base*(1+lam[product])).sum()-cent,abs_tol=1e-7)
    assert math.isclose(mm[2], -(base*(1-lam[product])).sum()-cent,abs_tol=1e-7)
    if n==30030:
        assert not raw[lam[product]<0].any()
        assert not raw[:,~unit].any()
    return dict(N=n,sample=int(n in sample),rows=len(d),cols=len(k),D=diag,G=g,O=off,
                O_scaled=off/n**1.5,O_over_D=off/diag,HL_O=hl,
                HL_trunc_abs_bound=trunc_err,V=v,V_over_N=v/n,Vraw=v+cent,center=cent,
                raw_mass=raw.sum(),C=row_center,HL_common=common_cov,V_common=common_proj,Vplus=pp[2],Vminus=mm[2],Oplus=pp[1],Ominus=mm[1])

rows=[analyze(n) for n in target]
with (OUT/'results.csv').open('w') as of:
    w=csv.DictWriter(of,fieldnames=rows[0])
    w.writeheader()
    w.writerows(rows)
def fit(rs):
    x=np.log([r['N'] for r in rs])
    y=np.log([abs(r['V']) for r in rs])
    b,a=np.polyfit(x,y,1)
    return (float(b),float(np.corrcoef(x,y)[0,1]**2))
def report(name,rs):
    print(name,len(rs),'negative O',sum(r['O']<0 for r in rs),'HL negative',
          sum(r['HL_O']<0 for r in rs),'sign matches',sum(r['O']*r['HL_O']>0 for r in rs),
          'slope,R2',fit(rs))
    print('min,max |V|/N', min(abs(r['V_over_N']) for r in rs),max(abs(r['V_over_N']) for r in rs))
    print('normalized O min,max',min(r['O_scaled'] for r in rs),max(r['O_scaled'] for r in rs))
    print('HL observed normalized Pearson',np.corrcoef([r['O_scaled'] for r in rs],
              [r['HL_O']/r['N']**1.5 for r in rs])[0,1])
def subset(numbers): return [r for r in rows if r['N'] in numbers]
report('special',subset(special))
report('powers',subset(powers))
report('prime squares',subset(squares))
report('highly composite multiples',subset(multiples))
report('stratified sample',subset(sample))
print('N median, median abs(V), median |V|/N, median O/N^1.5, negative count')
bins=[]
for i in range(14,20):
    rs=[r for r in subset(sample) if 2**i <= r['N'] < 2**(i+1)]
    med=np.median
    b=dict(N=med([r['N'] for r in rs]),V=med([abs(r['V']) for r in rs]))
    bins.append(b)
    print(b['N'],b['V'],med([abs(r['V_over_N']) for r in rs]),
          med([r['O_scaled'] for r in rs]),sum(r['O']<0 for r in rs))
print('median-bin slope,R2',fit(bins))
print('structured rows: N, O, HL, V, Vplus, Vminus')
for r in subset(special):
    print(r['N'],*(round(r[k],2) for k in ['O','HL_O','V','Vplus','Vminus']))
for n in wave1:
    observed={100000:-26073.0,126002:-9799.1,131072:-64357.2,200000:-62578.1,500000:-63177.5}
    assert abs(subset([n])[0]['O']-observed[n])<0.06
```

</details>

<details><summary>Lean source</summary>

```lean
import Mathlib

namespace ArithmeticFunction

def liouville : ArithmeticFunction ℤ :=
  ⟨fun m => if m = 0 then 0 else (-1 : ℤ) ^ cardFactors m, by simp⟩

end ArithmeticFunction

open ArithmeticFunction
open scoped BigOperators

namespace GoldbachAttack

private theorem two_factors {m : ℕ} {z : ℝ} (hm : 1 < m) (hsize : (m : ℝ) < z ^ 3)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ m → z < (p : ℝ)) (hc : ¬ m.Prime) :
    cardFactors m = 2 := by
  have hm0 : m ≠ 0 := by omega
  have hmin := Nat.minFac_prime (show m ≠ 1 by omega)
  have hzmin := hrough _ hmin (Nat.minFac_dvd m)
  have hprod : m.minFac ^ m.primeFactorsList.length ≤ m := by
    calc
      _ ≤ m.primeFactorsList.prod := List.pow_card_le_prod _ _ (fun p hp =>
        Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactorsList hp).two_le
          (Nat.dvd_of_mem_primeFactorsList hp))
      _ = m := Nat.prod_primeFactorsList hm0
  have hlen : m.primeFactorsList.length ≤ 2 := by
    by_contra! h
    have h3 := (Nat.pow_le_pow_right hmin.pos (show 3 ≤ m.primeFactorsList.length by omega)).trans hprod
    have h3r : (m.minFac : ℝ) ^ 3 ≤ m := by exact_mod_cast h3
    have hz : 0 ≤ z := by
      by_contra! hneg
      have : z ^ 3 ≤ 0 := by rw [pow_succ]; exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hneg.le
      have : (0 : ℝ) ≤ m := by positivity
      linarith
    linarith [pow_le_pow_left₀ hz hzmin.le 3]
  have hne0 : m.primeFactorsList.length ≠ 0 := by
    intro he
    have he' : m.primeFactorsList = [] := by simpa using he
    rcases (Nat.primeFactorsList_eq_nil m).mp he' with h | h <;> omega
  have hne1 : cardFactors m ≠ 1 := fun h => hc (cardFactors_eq_one_iff_prime.mp h)
  rw [cardFactors_apply] at hne1 ⊢
  omega

theorem weighted_prime_mass_cuberough
    (s : Finset ℕ) (z : ℝ) (a : ℕ → ℝ)
    (ha : ∀ m, 0 ≤ a m)
    (hs : ∀ m, a m ≠ 0 → m ∈ s ∧ 1 < m ∧ (m : ℝ) < z ^ 3 ∧
      ∀ p : ℕ, p.Prime → p ∣ m → z < (p : ℝ)) :
    (∑ m ∈ s, if m.Prime then a m else 0) =
      ((∑ m ∈ s, a m) - ∑ m ∈ s, a m * (liouville m : ℝ)) / 2 := by
  rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0), Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  by_cases h : a m ≤ 0
  · simp [le_antisymm h (ha m)]
  obtain ⟨_, hm, hsize, hrough⟩ := hs m (ne_of_gt (lt_of_not_ge h))
  have hm0 : m ≠ 0 := by omega
  by_cases hp : m.Prime
  · simp [hp, liouville, hm0, cardFactors_apply_prime hp] ; ring
  · simp [hp, liouville, hm0, two_factors hm hsize hrough hp]

theorem exists_positive_prime_of_cuberough_strict
    (s : Finset ℕ) (z : ℝ) (a : ℕ → ℝ)
    (ha : ∀ m, 0 ≤ a m)
    (hs : ∀ m, a m ≠ 0 → m ∈ s ∧ 1 < m ∧ (m : ℝ) < z ^ 3 ∧
      ∀ p : ℕ, p.Prime → p ∣ m → z < (p : ℝ))
    (hlt : (∑ m ∈ s, a m * (liouville m : ℝ)) < ∑ m ∈ s, a m) :
    ∃ m ∈ s, m.Prime ∧ 0 < a m := by
  have hid := weighted_prime_mass_cuberough s z a ha hs
  by_contra! h
  have hle : (∑ m ∈ s, if m.Prime then a m else 0) ≤ 0 :=
    Finset.sum_nonpos fun m hm => by split_ifs with hp; exact h m hm hp; rfl
  linarith

end GoldbachAttack

def B004DyadicProjectorStatement : Prop :=
  ∀ k h : ℕ, 2 ≤ k →
    (∑ d ∈ (Nat.gcd (2 ^ k) h).divisors,
      ArithmeticFunction.moebius ((2 ^ k) / d) * (Nat.totient d : ℤ)) =
      (if 2 ^ k ∣ h then (Nat.totient (2 ^ k) : ℤ) else 0) -
      (if 2 ^ (k - 1) ∣ h then (Nat.totient (2 ^ (k - 1)) : ℤ) else 0)

theorem b004_dyadic_projector : B004DyadicProjectorStatement := by
  intro k h hk
  let s := (Nat.gcd (2 ^ k) h).divisors
  have hg : Nat.gcd (2 ^ k) h ≠ 0 := Nat.gcd_ne_zero_left (by positivity)
  have hprev : 2 ^ (k - 1) ∣ (2 : ℕ) ^ k := pow_dvd_pow _ (by omega)
  have hneq : (2 : ℕ) ^ k ≠ 2 ^ (k-1) := by
    have := Nat.pow_lt_pow_right (by decide : 1 < 2) (show k-1 < k by omega)
    omega
  have htop : (2 : ℕ) ^ k ∈ s ↔ 2 ^ k ∣ h := by simp [s, Nat.mem_divisors, Nat.dvd_gcd_iff, hg]
  have hsub : (2 : ℕ) ^ (k-1) ∈ s ↔ 2 ^ (k-1) ∣ h := by
    simp [s, Nat.mem_divisors, Nat.dvd_gcd_iff, hg, hprev]
  change (∑ d ∈ s, _) = _
  calc
    _ = ∑ d ∈ s, ((if 2 ^ k = d then (Nat.totient (2 ^ k) : ℤ) else 0) -
        (if 2 ^ (k-1) = d then (Nat.totient (2 ^ (k-1)) : ℤ) else 0)) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdvd := (Nat.mem_divisors.mp hd).1
      obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
        (dvd_trans hdvd (Nat.gcd_dvd_left _ _))
      have hdiv : (2 : ℕ) ^ k / 2 ^ j = 2 ^ (k-j) := by
        conv_lhs => lhs; rw [← Nat.sub_add_cancel hj, pow_add]
        simp
      rw [hdiv]
      rcases eq_or_lt_of_le hj with rfl | hj'
      · simp [hneq.symm]
      · have hkj : (2 : ℕ) ^ k ≠ 2 ^ j := ne_of_gt (Nat.pow_lt_pow_right (by decide) hj')
        rw [moebius_apply_prime_pow Nat.prime_two (by omega), if_neg hkj]
        by_cases he : j = k-1
        · subst j
          have he' : k - (k-1) = 1 := by omega
          simp [he']
        · have hp : (2 : ℕ) ^ (k-1) ≠ 2 ^ j :=
            ne_of_gt (Nat.pow_lt_pow_right (by decide) (by omega))
          simp [hp, show k-j ≠ 1 by omega]
    _ = _ := by simp [Finset.sum_sub_distrib, htop, hsub]

#print axioms GoldbachAttack.weighted_prime_mass_cuberough
#print axioms GoldbachAttack.exists_positive_prime_of_cuberough_strict
#print axioms b004_dyadic_projector
```

</details>

# B-012 · Shifted Mangoldt weights against the parity models

[P] At all five targets, the genuine Liouville sum on cube-root-rough complements was negative. Its ratio to rough mass ranged from −0.343192 to −0.316342. The plus model has ratio +1 identically. A second difference occurs in the balanced quadratic form of equation (4). Both synthetic signs generate a large positive off-diagonal. Section 3 proves an order-of-magnitude obstruction for those models on the infinite family of powers of two, using the prime number theorem. [U] The upper estimate for the genuine quadratic form, and uniform positive prime mass at fixed even targets, remain open in this analysis.

[Q] Tags follow the B-003 audit. [Q] denotes a sourced statement, [P] a derivation shown here or a finite computation actually run, [I] an interpretation, and [U] an unverified or conditional assertion. No new result here has a repository strict-check verdict. [Issue and start comment](https://github.com/nisbenz/goldbach-grh-lean/issues/9#issuecomment-7223154368)

## 1. Measures and exact identities

[Q] Fix an even target N, use natural logarithms, and let λ(m) = (−1)^Ω(m), with multiplicity. In the experiment 1 < m < N and (m,N)=1. The genuine weight is Λ(N−m), including higher prime powers. The two synthetic weights are w(m)(1±λ(m))/K₀. On this domain w(m) is the product of (p−1)/(p−2) over the distinct prime divisors of m. Outside the coprime domain the synthetic weights vanish. The normalizer is K₀=(φ(N)/N)∏_{p∤N}(1+1/[p(p−2)]). There is no factor 1/2 in the definition. [Matched divisor tests and Vaughan decomposition](../../proof/strong_goldbach_research.md#3-attack-2--divisor-decompositions-and-a-matched-parity-countermodel)

[P] The Goldbach singular series equals the **inverse** normalizer. At an odd prime outside N the factor of K₀⁻¹ is p(p−2)/(p−1)². At an odd prime dividing N it is p/(p−1), whose ratio to that outside-N factor is (p−1)/(p−2). The prime 2 contributes 2. Thus K₀⁻¹ = 2∏_{p>2}(1−1/(p−1)²)∏_{p|N, p>2}(p−1)/(p−2) = 𝔖(N). This shared local normalization cannot distinguish either parity sign. Computations truncate the product at T=10⁶. The omitted log of K₀ is positive and at most ∑_{j>T}1/[j(j−2)] = (1/(T−1)+1/T)/2. The absolute synthetic masses therefore have a relative normalization error below 1.00001·10⁻⁶, apart from roundoff. An overall scale cancels in B/S and B/U. Centered dispersion sums use the displayed truncation.

[P] Let R={1<m<N : (m,N)=1, spf(m)³>N}, where spf denotes the smallest prime factor. For a nonnegative weight on R write S=∑a, Q=∑_{m=r²}a_m, B=∑a_mλ(m), and P=∑_{m prime}a_m. Every m in R has either one or two prime factors with multiplicity. Therefore P=(S−B)/2, including squares. Since λ(r²)=1 and μ(r²)=0, the Möbius version is P=(S−Q−∑a_m μ(m))/2. Removing Q twice would change the answer.

[P] For S>0 and any real c, B≤(1−c)S is **equivalent to P≥cS/2**. Strict B<S is equivalent to P>0. A useful version in factorization variables lets H be the mass over ordered prime pairs (r,s) with rs∈R, weighted by a_{rs} once per pair. Each square contributes once and each other semiprime twice, so H+Q=2(S−P) and B=H+Q−S. An independently proved lower bound S≥L>0 and upper bound H+Q≤(2−c)L, for 0<c≤2, imply P≥cS/2. These bounds describe the required supply and semiprime estimates precisely.

[P] Write E for the part of genuine P with N−m=pʲ, j≥2. A rough **two-prime** representation exists exactly when S−B>2E. A crude bound is E≤√N log N, since each base p≤√N contributes at most log N after summing all its exponents. A uniform fractional saving and a uniform rough supply of order N/log N would overwhelm E for large N. Positive Λ-weighted P alone allows the reflected input to be a prime power.

## 2. Finite head-to-head

[P] All table entries in this section are computed. The inputs include 2¹⁷ and 2·251². Masses below use natural-log weights, and the counts are integers. Both synthetic sequences use the same normalization and cutoffs. The scratch script and raw JSON are linked at the end, with a recoverable copy of the program in the appendix.

### Rough detector

[P] P is the direct sum over rough primes. The script checks it against (S−B)/2 and checks B−∑aμ=Q on every row.

| N | Weight | S | Q | B | P | B/S |
|---|---|---|---|---|---|---|
| 100000 | true | 25,234.39 | 0.00 | -8,660.25 | 16,947.32 | -0.343192 |
| 100000 | plus | 16,516.04 | 180.94 | 16,516.04 | 0.00 | +1.000000 |
| 100000 | minus | 33,726.61 | 0.00 | -33,726.61 | 33,726.61 | -1.000000 |
| 126002 | true | 22,942.44 | 187.74 | -7,827.25 | 15,384.85 | -0.341169 |
| 126002 | plus | 15,123.58 | 146.83 | 15,123.58 | 0.00 | +1.000000 |
| 126002 | minus | 31,295.56 | 0.00 | -31,295.56 | 31,295.56 | -1.000000 |
| 131072 | true | 24,135.78 | 192.85 | -8,188.68 | 16,162.23 | -0.339275 |
| 131072 | plus | 16,015.32 | 151.54 | 16,015.32 | 0.00 | +1.000000 |
| 131072 | minus | 32,313.80 | 0.00 | -32,313.80 | 32,313.80 | -1.000000 |
| 200000 | true | 48,349.37 | 310.86 | -15,294.93 | 31,822.15 | -0.316342 |
| 200000 | plus | 33,163.80 | 247.88 | 33,163.80 | 0.00 | +1.000000 |
| 200000 | minus | 63,266.71 | 0.00 | -63,266.71 | 63,266.71 | -1.000000 |
| 500000 | true | 110,991.25 | 371.05 | -36,894.04 | 73,942.65 | -0.332405 |
| 500000 | plus | 74,105.10 | 367.52 | 74,105.10 | 0.00 | +1.000000 |
| 500000 | minus | 146,175.93 | 0.00 | -146,175.93 | 146,175.93 | -1.000000 |

[P] The column E measures contamination of P by reflected higher powers. The final column is rough plus mass on points where the reflected integer has Λ=0. This single support test already distinguishes the base model. A second implementation using Eratosthenes sieving, crossing out small prime factors of m and enumerating reflected prime powers, reproduced S, P and the ordered rough pair counts for the genuine weights on all five targets.

| N | Reflected higher-power mass E | Ordered rough prime pairs | Plus mass where Λ(N−m)=0 |
|---|---|---|---|
| 100000 | 18.74 | 1618 | 13,620.12 |
| 126002 | 113.00 | 1427 | 13,164.22 |
| 131072 | 108.86 | 1496 | 13,975.53 |
| 200000 | 164.70 | 2834 | 27,740.19 |
| 500000 | 217.17 | 6101 | 63,004.62 |

### Ordered factorization sums

[P] Use 1<dk<N and (dk,N)=1. The squarefree range allows 1 as a factor and requires each factor to be squarefree and at most √N. The Vaughan range allows every integer factor between the actual real endpoints N^(1/3) and N^(2/3), inclusive, without a squarefreeness test. It is a sign diagnostic on the specified range. The genuine Vaughan identity has different coefficients. Each ordered factorization counts separately. For the synthetic columns B⁺=U⁺ and B⁻=−U⁻ exactly, by complete multiplicativity.

| N | Range | Pairs | Genuine U | Genuine B | Genuine B/U | U⁺ | U⁻ |
|---|---|---|---|---|---|---|---|
| 100000 | squarefree | 11448 | 33,314.26 | -1,779.33 | -0.053410 | 30,839.26 | 34,089.01 |
| 100000 | Vaughan | 46694 | 144,284.90 | 753.86 | +0.005225 | 143,773.24 | 144,490.79 |
| 126002 | squarefree | 20448 | 48,131.69 | -1,071.75 | -0.022267 | 47,989.30 | 49,035.16 |
| 126002 | Vaughan | 91947 | 242,159.92 | 2,830.09 | +0.011687 | 239,889.31 | 240,420.13 |
| 131072 | squarefree | 21608 | 50,306.55 | -1,325.01 | -0.026339 | 50,659.86 | 51,663.85 |
| 131072 | Vaughan | 97596 | 253,409.65 | -2,184.32 | -0.008620 | 253,486.83 | 253,839.06 |
| 200000 | squarefree | 22800 | 64,844.01 | -2,562.34 | -0.039515 | 62,462.59 | 67,101.75 |
| 200000 | Vaughan | 99804 | 306,174.45 | 940.95 | +0.003073 | 304,875.21 | 308,593.84 |
| 500000 | squarefree | 57599 | 163,686.56 | -6,350.89 | -0.038799 | 159,207.08 | 167,144.20 |
| 500000 | Vaughan | 269713 | 831,454.25 | -4,346.92 | -0.005228 | 832,295.01 | 837,467.77 |

[P] For any nonnegative coefficients on ordered pairs, (U−B)/2 counts their mass on products with odd Ω. In the Vaughan range d,k>1, all such products have **at least three prime factors**. They are all outside R. If one instead enforces dk∈R with d,k>1, each surviving product is a semiprime (possibly a square) and B=U even for the genuine weights. Hence cancellation in the unrestricted product box cannot be substituted into the rough identity.

### Centered off-diagonal, equation (4)

[P] Put h=⌊√(N−1)⌋ and take I=J=(⌊h/2⌋,h] on the integers, so dk<N across the entire box. The star requires (d,N)=(e,N)=1 and does not require (d,e)=1. Set X_d(k)=μ(d)(A(d,k)−d/φ(d)). The total quadratic form G=∑ₖ(∑d X_d(k))² includes the diagonal D=∑ₖ,d X_d(k)². Report O=G−D, the **ordered** off-diagonal d≠e. G and D are nonnegative, while O may have either sign. The program cross-checks the first three k columns of each run by directly summing the distinct pairs. [Definition of equation (4)](../../proof/strong_goldbach_erh_attack.md#replacing-d_2-by-primes)

[P] For the literal genuine equation, A=Λ(N−dk) for all k. A separate run applies the common mask (dk,N)=1 to the genuine coefficients. All five boxes give the same genuine totals with either convention. In general a deleted genuine term can be nonzero if N−dk is a power of a prime dividing N. Both synthetic rows use their native zero off the coprime domain. All four runs use d/φ(d) as the center per unrestricted k. Re-centering on coprime k alone defines a different experiment.

| N | I=J | Genuine D | Genuine O | Plus O | Minus O | O/N^(3/2), genuine | O/N^(3/2), plus |
|---|---|---|---|---|---|---|---|
| 100000 | 159–316 | 92,683.0 | -26,073.0 | 1,617,816.3 | 1,731,237.4 | -0.000825 | +0.051160 |
| 126002 | 178–354 | 145,326.1 | -9,799.1 | 2,934,152.5 | 2,909,393.7 | -0.000219 | +0.065602 |
| 131072 | 182–362 | 160,627.9 | -64,357.2 | 3,242,535.0 | 3,207,793.1 | -0.001356 | +0.068331 |
| 200000 | 224–447 | 199,903.9 | -62,578.1 | 4,646,235.0 | 4,703,391.6 | -0.000700 | +0.051946 |
| 500000 | 354–707 | 554,845.6 | -63,177.5 | 18,841,188.5 | 18,931,407.4 | -0.000179 | +0.053291 |

## 3. Why the models have a large off-diagonal

[P] Define Y(k)=∑_{d∈I,(d,N)=1} μ(d)(A(d,k)−c_d), c_d=d/φ(d), and let J₀=|J|. For either synthetic model let M±=∑_{k,d} μ(d)²a±_{dk} over this same rectangle. The signed projection obeys the exact identity

$$
 V_\pm=\sum_{k\in J}\lambda(k)Y_\pm(k)
 =\pm M_\pm-
 \left(\sum_{d\in I,(d,N)=1}\mu(d)c_d\right)
 \left(\sum_{k\in J}\lambda(k)\right).
$$

[P] Indeed a contributing d is squarefree, so μ(d)=λ(d). On the support of a±, μ(d)λ(k)=λ(dk)=±1. The centering factors separately even on k where the raw synthetic weight vanishes. Consequently G≥V²/J₀. For example at N=131072, V is +16649.63 for plus, −16676.02 for minus and +249.75 for the genuine coefficients. V²/(J₀G) is respectively 46.17%, 46.83% and 0.36%. Both model signs can therefore yield a large **positive** off-diagonal.

[P] **Infinite family.** For N=2ᵗ tending to infinity, these same intervals and the exact normalizer satisfy M± ≫ N, |V±| ≫ N, and O± ≫ N^(3/2). Here and below the constants in this paragraph are absolute. The classical prime number theorem gives ∑_{n≤x}μ(n)=o(x) and hence ∑_{n≤x}λ(n)=o(x) by λ(n)=∑_{r²|n}μ(n/r²), splitting the convergent ∑1/r² tail. The odd-index sum equals ∑_{n≤x}λ(n)+∑_{n≤x/2}λ(n). Each λ sign therefore occurs at (1/4+o(1))|J| odd indices of J. Also (4/π²+o(1))|I| integers in I are odd squarefree, by summing μ(r) over odd square divisors. For each such d, either requested sign of λ(dk) occurs on ≫|J| odd k. On those pairs a±_{dk}≥2/K₀, and K₀ is constant along this family. This proves the mass lower bounds.

[P] For the centering term ∑_{d≤h}d/φ(d)≪h, by d/φ(d)=∑_{r|d}μ(r)²/φ(r) and convergence of ∏ₚ(1+1/[p(p−1)]). The k-sum of λ is o(h), so centering changes V± by o(N). The projection bound gives G± ≫ N^(3/2). Finally w(m)≤2^ω(m)≤τ(m) and d/φ(d)≤τ(d); the standard divisor bound yields D±≪ε N^(1+ε), after rescaling ε. Subtracting D proves the claimed off-diagonal lower bound. This argument is unconditional on RH; the separate statement about the models matching the one-prime divisor main terms to high level uses RH.

[I] This rules out a blanket estimate O≤o(N^(3/2)/log² N) for these synthetic coefficients, even if a proof were allowed to retain their matched divisor densities. The squared norm tests every direction in k, including λ(k). The particular Vaughan coefficient has another shape, so a bound tailored to that coefficient could be weaker than controlling the full norm. The observed sign of the genuine O is a finite result.

## 4. Which observables separate the measures

[P] On a finite domain every linear test f separates the base plus measure from the true measure exactly if ∑f(m)(a⁺_m−aᵗʳᵘᵉ_m)≠0. This also describes all accidental equalities. More informative concrete tests are the rough prime indicator and its λ equivalent, the multiplicity-weighted factorization signs, reflected support, and the centered two-form statistic computed above. The scalar 𝔖(N) is shared by the local model and the expected Goldbach main term. Even exact agreement of that scalar leaves the rough prime indicator unconstrained.

[P] For example at N=100000, m=47² lies in R with positive plus weight, but N−m=97791 is a multiple of 3 greater than 3 and indivisible by 9, so Λ(N−m)=0. In general the base model assigns weight to reflected composite nonpowers. Conversely on any rough prime m with prime N−m the plus weight is zero. The reflected nonpower column in §2 measures the first divergence even without selecting primes m.

[Q] A prescribed *finite* system of reflected residue tests can be built into a modified parity model by conditioning on (N−m,W)=1 and changing the corresponding Euler factors. A Dirichlet character in m is multiplicative, while a class function of Frob at N−m is naturally defined on unramified reflected primes and requires an explicit extension to test a synthetic integer measure. Fixed-field Chebotarev under Artin holomorphy and the specified ERH gives one-prime progression errors of size O_K(√N log²(Nd)) for fixed test data. The tests at m and at N−m have different coefficients. [Reflected tests](../../proof/strong_goldbach_research.md#3-attack-2--divisor-decompositions-and-a-matched-parity-countermodel) · [Field dependence](../../proof/strong_goldbach_erh_attack.md#1-what-an-extra-frobenius-condition-measures)

[I] The explicit support witness rejects the unmodified model. It supplies neither a persistent discrepancy for every locally conditioned model nor a growing-field Chebotarev theorem. Agreement of a chosen character correlation is possible. In particular the automorphic estimate in §4 of the ERH notes concerns a signed difference of model weights; it does not identify the genuine value of an arbitrary reflected statistic.

[P] In the literal off-diagonal the two forms in k obey e(N−dk)−d(N−ek)=N(e−d). For a prime ℓ not dividing Nde, the two forbidden classes of k coincide exactly when ℓ divides e−d. The local avoidance fraction is then 1−1/ℓ, compared with 1−2/ℓ for distinct classes. Thus subtracting the two first-moment centers does not remove all local covariance. Transposing the Cauchy step instead yields Λ(N−dk₁)Λ(N−dk₂) with k₂(N−dk₁)−k₁(N−dk₂)=N(k₂−k₁). A proof must retain or bound these correlations after the Möbius signs and the chosen weights. Treating every distinct pair as independent would silently delete a term.

## 5. Estimates tested against the fixed target

[P] Write L=log N. For d,k of length ≍√N in one box, |b_k|≤L implies ‖b‖₂²≪√N L². The genuine diagonal is O(N L²), since Λ≤L and d/φ(d)≪log N. Thus a uniform one-sided O≤o(N^(3/2)/L²) suffices for the centered Vaughan box to be o(N), by equation (4). Taking absolute values term by term costs O(N^(3/2)L²). The gap **in this upper-bound comparison** is four logarithmic powers and a little-o saving, with additional losses possible from combining boxes. It is not a necessary condition for any proof: cancellation with the specific b_k could suffice. Even this one-box result would still require the other terms, box summation and a positive main term. [Equation (4)](../../proof/strong_goldbach_erh_attack.md#replacing-d_2-by-primes)

| Input | Scope and obstruction in this application |
|---|---|
| Dirichlet GRH / ERH and the linear sieve | [Q] A single genuine progression has error O(√N L²). [P] Summing allowances up to N^α costs N^(1/2+α)L² and exhausts the N scale at α=1/2. For z=N^(1/3), the lower sieve needs s=3α>2. Even the **unsigned** lower estimate by this route needs α>2/3, a gap of 1/6 from 1/2. For every fixed δ>0 the model under RH has the prescribed divisor main terms with a summed power-saving error through N^(1−δ), and has P=0. This is a statement about the model. The genuine weights have no such level established here. A better unsigned supply by itself leaves B undetermined. [Divisor test](../../proof/strong_goldbach_research.md#3-attack-2--divisor-decompositions-and-a-matched-parity-countermodel) |
| Matomäki–Radziwiłł and Matomäki–Radziwiłł–Tao | [Q] The short-interval theorem gives typical interval control and an unrestricted fixed-shift Liouville correlation saving. The averaged Chowla theorem gives o(HᵏX) summed over k shifts. [P] Even a single shift tuple contributing order X to the latter sum is compatible with that bound when H→∞. The fixed-shift saving for λ(n)λ(n+1) has neither the reflected Λ coordinate nor the rough restriction. An o(N) error for a full log-weighted sum could conceal the entire expected N/log N rough signal. No exponent for a single two-form prime box is specified by either theorem. [Short intervals](https://arxiv.org/abs/1501.04585) · [Averaged Chowla](https://arxiv.org/abs/1503.05121) |
| Vaughan and Heath-Brown identities | [Q] Vaughan's balanced term has μ(d) times b_k=∑_{v∣k,v>V}Λ(v). A Heath-Brown decomposition yields more signed divisor variables. [P] Exact rewritings incur no numerical exponent loss themselves. Summing separate progression allowances over ≍√N possible d costs O(N L²) even for a free inner variable. With b_k present even that free-variable estimate is unavailable. The actual missing saving is in the signed two-form sum above or an estimate for the specific b_k. [Decomposition and transposed dispersion](../../proof/strong_goldbach_research.md#4-attack-3--dispersion-zero-statistics-and-transference) |
| Bombieri–Friedlander–Iwaniec and Maynard | [Q] The classical well-factorable level 4/7 and Maynard's triply well-factorable 3/5 concern weighted modulus averages for actual primes. Maynard's theorem has a fixed residue a with the implied constant depending on a. His uniform-residue version controls moduli with suitably sized factors and a different error term. [P] Even granting the first two levels for every required sieve weight uniformly at a=N, their deficits from 2/3 are 2/21 and 1/15. Both are one-prime estimates. Maximizing over residues in a one-prime estimate does not insert Λ(N−ek) in the inner k-sum. [Maynard II, Thm. 1.1 and BFI comparison](https://arxiv.org/html/2006.07088) · [Maynard III, Thm. 1.1](https://arxiv.org/html/2006.08250) |
| Pascadi, prime progression estimates | [Q] Theorem 1.3 gives 5/8−ε for triply well-factorable weights and 3/5−ε for the specified upper linear-sieve weights, with an a-dependent constant. [P] Even the larger exponent falls 1/24 short of 2/3. Extending it to the signed quadratic form would also change the coefficient and quantifier. [Theorem 1.3](https://arxiv.org/html/2505.00653) |
| Pascadi, Kloosterman fractions and unbalanced convolution | [Q] Theorem 5.2 imposes 0<abs(a)≤x/12, a Siegel–Walfisz short factor y, and, among other conditions, Q≤x^(−ε)(x²⁰⁷/y⁴⁶⁸)^(1/389). [P] To exceed Q=x^(1/2) by this constraint with y=x^ν requires ν<25/936 before ε; a balanced factor has ν≈1/2. Taking a=N for products ≤N also fails the size condition in the direct dyadic application. Theorem 5.3 has smooth determinant coefficients; matching its determinant alone does not transform two Mangoldt factors into those coefficients. [Theorems 5.2–5.3](https://arxiv.org/html/2611.34917) |
| Weil, Voronoi, spectral dispersion | [Q] For smooth d₂ coefficients the repository derives per-modulus Oε(N^ε d^(1/2)), summed Oε(N^ε D^(3/2)), and a reflected d₂,d₂ error Oε(N^(3/4+ε)). [P] At D≈√N the divisor error saves 1/4 in the power over N, while the summed one-prime GRH allowance saves zero. The dual length q²/N in the divisor formula has no justified counterpart here for Λ or the rough cutoff. A Kloosterman bound on a complete nonzero frequency leaves zero frequencies, diagonal terms and correlations between moduli to be estimated. [Spectral calculation](../../proof/strong_goldbach_erh_attack.md#2-a-spectral-calculation-that-works-and-the-balanced-sum-that-remains) |
| Supplied shifted Möbius and Chen inputs | [Q] The repository describes a fixed-shift Möbius prime average and a prime-factor-extraction weight W. [P] Every extracted prime is below N^θ for each fixed θ>0 eventually, hence W vanishes identically on R. Even a reflected unrestricted o(N/log N) unweighted error permits loss of a whole rough prime-pair signal of order N/log² N. [Q] Chen supplies a uniform positive baseline on the larger at-most-two-factor candidate set; the sign bias on that set still needs an independent bound. [Cutoff and Chen reduction](../../proof/strong_goldbach_erh_attack.md#3-the-2026-möbius-mechanism-at-the-goldbach-cutoff) |

[I] The deficits refer to those substitutions and upper bounds. They do not give a sharp exponent for all dispersion methods. [U] No estimate above establishes the required pointwise upper bound for the genuine signed term under ERH, or the inequality S−B>2E for all sufficiently large even N.

## 6. Proposed Lean 4 micro-lemma

[U] The following are exact proposed declaration **headers**, followed by a mathematical proof sketch. The real cutoff allows z=N^(1/3) for noncubic N. A finite set s contains the support of a, and zero terms may be padded freely. The project declares Liouville with values in ℤ, so the cast occurs before the real division. These declarations have no kernel or strict-check verdict. [Existing natural-cutoff detector](../lean/Goldbach/Detector.lean)

```lean
import Goldbach.Detector

open ArithmeticFunction
open scoped BigOperators

namespace GoldbachAttack

theorem weighted_prime_mass_cuberough
    (s : Finset ℕ) (z : ℝ) (a : ℕ → ℝ)
    (ha : ∀ m, 0 ≤ a m)
    (hs : ∀ m, a m ≠ 0 → m ∈ s ∧ 1 < m ∧ (m : ℝ) < z ^ 3 ∧
      ∀ p : ℕ, p.Prime → p ∣ m → z < (p : ℝ)) :
    (∑ m ∈ s, if m.Prime then a m else 0) =
      ((∑ m ∈ s, a m) - ∑ m ∈ s, a m * (liouville m : ℝ)) / 2

theorem exists_positive_prime_of_cuberough_strict
    (s : Finset ℕ) (z : ℝ) (a : ℕ → ℝ)
    (ha : ∀ m, 0 ≤ a m)
    (hs : ∀ m, a m ≠ 0 → m ∈ s ∧ 1 < m ∧ (m : ℝ) < z ^ 3 ∧
      ∀ p : ℕ, p.Prime → p ∣ m → z < (p : ℝ))
    (hlt : (∑ m ∈ s, a m * (liouville m : ℝ)) < ∑ m ∈ s, a m) :
    ∃ m ∈ s, m.Prime ∧ 0 < a m

end GoldbachAttack
```

[P] For each nonzero term, 1<m<z³ implies z>1. The list of prime factors is nonempty and has product m. If it has at least three entries, choose its first three. Each exceeds z and every remaining factor is at least one, so their product exceeds z³, a contradiction. Thus the list length is one or two. Reuse the B-017 argument via cardFactors_apply, cardFactors_eq_one_iff_prime and liouville_apply: a prime has λ=−1 and a composite on this support has λ=1. For a natural cutoff one may use B-017 directly together with λ∈{−1,1} for m≠0. That extra sign fact licenses the passage from its integer quotient to a real identity. For a real cutoff use the preceding three-factor argument; rounding z down in the upper bound m<z³ could lose valid m. In each case 2 times the prime-filtered summand equals a(m)(1−λ(m)). This also holds for a(m)=0. Sum over s, distribute subtraction and divide by two in ℝ. Under hlt the prime-filtered sum is positive. If every prime in s had weight ≤0, each summand would be ≤0, contradicting positivity. Nonnegativity is natural for the mass interpretation and is stronger than needed for these two implications.

## 7. Reproduction

[P] Run the following from any directory. The JSON includes full-precision displayed binary64 results for all four dispersion runs and their diagonal and projection checks. All cutoff, primality, squarefreeness and pair-membership decisions are integer operations. Python optimization should be off to execute the assertions. [Program](/tmp/astra_b012/compare.py) · [Raw output](/tmp/astra_b012/results.json)

```sh
python3 /tmp/astra_b012/compare.py > /tmp/astra_b012/results.json
```

[P] The appendix preserves the same program in case the scratch directory is cleared. Save the Python block below as compare.py and run it with Python 3.11 or later.

```python
"""[P] Reproduce B-012 tables with Python 3.11+ (standard library)."""
from argparse import ArgumentParser
from array import array
from itertools import combinations
from math import expm1, fsum, gcd, isclose, isqrt, log, log1p
import json


def arithmetic(limit):
    spf = array('I', range(limit + 1))
    for p in range(2, isqrt(limit) + 1):
        if spf[p] == p:
            for n in range(p*p, limit+1, p):
                if spf[n] == n:
                    spf[n] = p
    liouville = array('b', [1]) * (limit+1)
    mu = array('b', [1]) * (limit+1)
    mangoldt = array('d', [0]) * (limit+1)
    phi = array('I', [1]) * (limit+1)
    w = array('d', [1]) * (limit+1)
    for n in range(2, limit+1):
        p = spf[n]
        t = n // p
        liouville[n] = -liouville[t]
        repeated = t % p == 0
        phi[n] = phi[t] * (p if repeated else p-1)
        mu[n] = 0 if repeated else -mu[t]
        w[n] = w[t] if repeated or p == 2 else w[t] * (1+1/(p-2))
        if p == n:
            v = p
            while v <= limit:
                mangoldt[v] = log(p)
                v *= p
    return spf, liouville, mu, mangoldt, phi, w


def cube_floor(n):
    lo, hi = 0, n+1
    while hi-lo > 1:
        m = (lo+hi)//2
        if m**3 <= n:
            lo = m
        else:
            hi = m
    return lo


def close(a, b):
    assert isclose(a, b, rel_tol=2e-11, abs_tol=1e-7), (a, b)


def experiment(n, cutoff, data):
    spf, lam, mu, mangoldt, phi, w = data
    assert n % 2 == 0 and n >= 100 and cutoff >= n
    log_k = log(phi[n]/n) + fsum(log1p(1/(p*(p-2))) for p in range(3, cutoff+1, 2)
                                  if spf[p] == p and n % p)
    inverse_k = 1 + expm1(-log_k)
    names = ('true', 'plus', 'minus')
    weights = {name: array('d', [0]) * n for name in names}
    for m in range(2, n):
        if gcd(m, n) == 1:
            weights['true'][m] = mangoldt[n-m]
            weights['plus'][m] = inverse_k * w[m] * (1+lam[m])
            weights['minus'][m] = inverse_k * w[m] * (1-lam[m])
    rough = [m for m in range(2, n) if spf[m]**3 > n and gcd(m,n)==1]
    squares = [m for m in rough if isqrt(m)**2 == m]
    primes = [m for m in rough if m == spf[m]]
    result = {'N':n, 'inverse_K':inverse_k, 'rough':{}, 'bilinear':{}, 'dispersion':{}}
    for name, a in weights.items():
        S = fsum(a[m] for m in rough)
        B = fsum(a[m]*lam[m] for m in rough)
        Q = fsum(a[m] for m in squares)
        P = fsum(a[m] for m in primes)
        close(P, (S-B)/2)
        close(B-fsum(a[m]*mu[m] for m in rough), Q)
        if name != 'true':
            close(B, S if name == 'plus' else -S)
        result['rough'][name] = dict(S=S,Q=Q,B=B,P=P,ratio=B/S)
    result['prime_powers_in_P'] = fsum(weights['true'][m] for m in primes if spf[n-m]!=n-m)
    result['rough_prime_pairs'] = sum(spf[n-m] == n-m and n-m>1 for m in primes)
    result['plus_mass_reflected_nonpowers'] = fsum(weights['plus'][m] for m in rough if mangoldt[n-m]==0)

    # Ordered pairs. A factor 1 is allowed in the first range, but dk > 1.
    root = isqrt(n)
    c = cube_floor(n)
    low = c + (c**3 != n)
    high = cube_floor(n*n)
    for label, first, last in [('squarefree',1,root), ('Vaughan',low,high)]:
        counts = array('I', [0])*n
        for d in range(first, last+1):
            if gcd(d,n)>1 or (label=='squarefree' and mu[d]==0):
                continue
            for k in range(first, min(last,(n-1)//d)+1):
                if gcd(k,n)>1 or d*k==1 or (label=='squarefree' and mu[k]==0):
                    continue
                assert lam[d]*lam[k] == lam[d*k]
                counts[d*k] += 1
        support = [m for m,cnt in enumerate(counts) if cnt]
        table = {'ordered_pairs':sum(counts)}
        for name, a in weights.items():
            U = fsum(counts[m]*a[m] for m in support)
            B = fsum(counts[m]*a[m]*lam[m] for m in support)
            table[name] = dict(U=U,B=B,ratio=B/U)
            if name!='true':
                close(B, U if name=='plus' else -U)
        result['bilinear'][label] = table

    top = isqrt(n-1)
    box = range(top//2+1,top+1)
    rows = [d for d in box if gcd(d,n)==1 and mu[d]]
    result['box'] = [box.start,top,len(rows),len(box)]
    # Shared centering d/phi(d) in all runs. 'literal' is eq. (4).
    for name in ('literal','true','plus','minus'):
        norms, diags, proj, crosscheck = [], [], [], []
        for i,k in enumerate(box):
            col = [mu[d] * ((mangoldt[n-d*k] if name=='literal' else weights[name][d*k])
                            -d/phi[d]) for d in rows]
            total = fsum(col)
            norms.append(total**2)
            diags.append(fsum(v*v for v in col))
            proj.append(lam[k]*total)
            if i<3:
                crosscheck.append(2*fsum(u*v for u,v in combinations(col,2)))
                close(norms[-1]-diags[-1],crosscheck[-1])
        total, diag, projection = fsum(norms),fsum(diags),fsum(proj)
        off = total-diag
        bound = projection**2/len(box)
        assert bound <= total+1e-7
        result['dispersion'][name] = dict(total=total,diagonal=diag,off=off,
                                         normalized=off/n**1.5,projection=projection,
                                         projected_fraction=bound/total)
    return result


if __name__ == '__main__':
    cli = ArgumentParser()
    cli.add_argument('--targets',nargs='+',type=int,default=[100000,126002,131072,200000,500000])
    cli.add_argument('--cutoff',type=int,default=1000000)
    opts = cli.parse_args()
    data = arithmetic(max(opts.cutoff,*opts.targets))
    print(json.dumps({'cutoff':opts.cutoff,'results':[experiment(n,opts.cutoff,data)
                                                     for n in opts.targets]},indent=2))
```

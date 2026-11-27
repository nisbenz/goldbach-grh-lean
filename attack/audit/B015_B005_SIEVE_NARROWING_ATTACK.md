# How much narrowing buys, and where the sign is lost

**[P]** The coefficient 200 in (13) is valid. A uniform evaluation of the two-dimensional Selberg denominator gives 8 in the same limsup bound. At the supplied margins this buys exponents 1.899989 and 1.39890, respectively. The first deduction uses the reported unconditional supply and the second also assumes WEH(0.999). **[U]** Both supply theorems are unverified inputs here. **[P]** A prime-free sequence can pay for either narrower baseline. A change of mark can eliminate overcounting in (8), but the resulting signed estimate would already measure the genuine rough prime-pair mass.

**[Q]** Source equations (7)–(9) are in the [ERH report, §4](../../proof/strong_goldbach_erh_attack.md#4-what-survives-the-stronger-tests). Equations (13)–(15) are in the [persistent-push report, §4](../../proof/strong_goldbach_persistent_push.md#4-the-unbalanced-convolution-theorem-and-the-sieve-count). The [repository audit](REPO_AUDIT.md) inventories these as C24–C26 and C32. Tags here mean **[Q]** directly read or quoted, **[P]** derived here or computed with the described program, **[I]** interpretation, and **[U]** unverified external input or unresolved estimate. Analytic deductions below name their inputs. No blocker-level strict-check verdict was obtained.

## [P] Narrowing the semiprime band

**[Q,U]** Write \(L=\log N,\ t_x=(x-1)/x,\ S=\mathfrak S(N)\), for even \(N\). In \(D_{1,a}\) the complement is prime, or it is \(m=rq\) with \(r,q\) prime and \(r\le q^{a-1}\). For \(1<a<2\) this implies \(r<q\). In units \(SN/L^2\) the repository attributes lower margins \(c_{1.9}=0.0002\) and \(c_{1.4}=0.031\) to Li–Liu, the latter under WEH(0.999). The factor of two converts their reported \(C(N)=S/2\). The report also attributes a separate 1.894 double-sieve refinement to the manuscript. All these attributions remain [U].

**[P]** A lost candidate has \(m^{t_b}<r\le m^{t_a}\). Omitting \(m<N/L^4\) costs at most \(N/L^4\) candidates. Omitting \(r\mid N\) costs at most \(\omega(N)\), since \(r\mid p=N-m\) forces \(p=r\). Hence sum over \((N/L^4)^{t_b}<r\le N^{t_a}\), with \(r\nmid N\). For each such prime set \(X=N/r\). To bound the remaining loss it suffices to count \(n,N-rn\) both prime on \(1\le n<X\). For \(\ell\mid N\) the two prohibited roots coincide at zero. At \(\ell=r\) only \(n=0\bmod r\) is prohibited. Else there are two distinct roots. Thus \(\nu_\ell=1\) at \(\ell\mid Nr\), and 2 elsewhere. The local product is
\[
 S_{N,r}=\prod_\ell\frac{1-\nu_\ell/\ell}{(1-1/\ell)^2}
        = S\,\frac{r-1}{r-2}.
\]
Here \(r>2\) eventually and \(S\) is bounded below uniformly.

**[P]** Put \(g_\ell=\nu_\ell/\ell,\ h_\ell=g_\ell/(1-g_\ell)\). For a sieve support \(d\le Z\) of squarefree products of permitted primes, set \(G(Z)=\sum_d\prod_{\ell\mid d}h_\ell\). CRT gives \(Xg(d)+O(\nu(d))\) for the intersection of the forbidden classes, with multiplicative \(g,\nu\). The upper quadratic form has main term \(X\sum_k h(k)^{-1}(\sum_{k\mid d}\lambda_d g(d))^2\). Möbius inversion with \(\lambda_1=1\) and Cauchy–Schwarz give its minimum \(X/G(Z)\). The minimizing coefficients satisfy \(|\lambda_d|=\prod_{\ell\mid d}(1-g_\ell)^{-1}G_d(Z/d)/G(Z)\le1\), since products of terms in \(G_d(Z/d)\) with divisors of \(d\) are all included in \(G(Z)\). The CRT error summed over \(d,e\le Z\) is \(O(Z^2\max_{j\le Z^2}2^{\omega(j)})=Z^{2+o(1)}\), uniformly. Primes in either linear form at or below the sieving cutoff \(w\) add \(O(w+1)\).

**[P]** The source takes \(Z=X^{2/5}, w=Z^{1/3}\). In the product \(\prod_{\ell\le w}(1+h_\ell)\), normalized to mass one, the inclusion indicators are independent Bernoulli variables of means \(g_\ell\). Mertens gives \(E\log d\le 2\log w+O(1)\). Markov leaves mass at least \(1/3-o(1)\) at \(d\le Z\). Mertens' product gives \(\prod_{\ell\le w}(1-g_\ell)\le (1+o(1))S_{N,r}e^{-2\gamma}/\log^2 w\). Uniformity follows by bounding every omitted normalized factor below by \(1-(\ell-1)^{-2}\) for odd \(\ell\). The resulting coefficient in \(SX/\log^2 X\) tends from this upper estimate to \(3(15/2)^2e^{-2\gamma}=53.196202\ldots\), since \(r\to\infty\) uniformly. This validates the slack 200. Taking \(Z=X^\theta\) with fixed \(\theta<1/2\) and then \(\theta\uparrow1/2\) already yields \(108e^{-2\gamma}=34.04557\ldots\) by the same Markov argument.

### [P] A uniform coefficient of 8

**[P]** Sieve with all primes up to \(Z=X^\theta\), \(0<\theta<1/2\). Use reference root counts \(\nu^0_2=1,\ \nu^0_\ell=2\) for odd primes and put \(S_0=2\prod_{\ell>2}(1-(\ell-1)^{-2})\). The unrestricted Dirichlet series of the reference \(h^0(d)\), supported on squarefree \(d\), is
\[
 \prod_\ell (1+h^0_\ell \ell^{-s})=\zeta(1+s)^2 A(s),
 \qquad A(0)=\prod_\ell(1+h^0_\ell)(1-1/\ell)^2=S_0^{-1}.
\]
Indeed \(h^0_\ell=2/(\ell-2)\) at odd primes. The linear residual coefficient in \(A_\ell(s)\) is \(O(\ell^{-2})\) and the higher terms have coefficients \(O(\ell^{-2})\) or smaller. Thus \(A\) has absolutely summable coefficients at zero. Convolving with \(\tau(n)/n\) and using \(\sum_{n\le y}\tau(n)/n=\tfrac12\log^2 y+O(\log(2y))\) gives \(G_0(Z)\sim \log^2 Z/(2S_0)\) by dominated convergence. The last divisor sum follows by summing \(1/(ij)\) over \(ij\le y\).

**[P]** The comparison with this *fixed* reference is uniform in \(N,r\). For primes through \(Z\), couple the normalized products with the same independent uniforms. Since \(g_\ell\le g^0_\ell\), the actual random \(d\) divides the reference \(d_0\), so \(\Pr(d\le Z)\ge\Pr(d_0\le Z)\). Restoring the product masses gives
\[
 G_{N,r}(Z)\ \ge\ G_0(Z)\prod_{\ell\le Z}
      \frac{1+h_\ell}{1+h^0_\ell}
 \ \ge\ G_0(Z) S_0/S_{N,r}.
\]
The last inequality extends a product of factors at most one to all primes. This step avoids applying a fixed-singular-series asymptotic with a changing modulus. Consequently the two-prime upper bound is \((2/\theta^2+o(1))S_{N,r}X/\log^2 X\). The remainder \(Z^{2+o(1)}+O(Z)\) is negligible for each fixed \(\theta<1/2\). Take the limsup in \(N\) *first*, then \(\theta\uparrow1/2\). This yields coefficient 8 in (13); it supplies neither an effective threshold nor a claim of optimality over other sieves. Ordinary Brun–Titchmarsh for one progression bounds just one primality condition and does not by itself supply the second logarithm.

**[P]** Uniformly \(X\ge N^{1-t_a}\), and the reciprocal-prime sum over the band tends to \(\log(t_a/t_b)\). For either valid coefficient \(C\), the displayed loss is therefore at most \(C a^2\log(t_a/t_b)\) in limsup. Keeping the \(r\)-dependence improves this to \(C\int_{t_b}^{t_a}du/[u(1-u)^2]\) by partial summation. Its antiderivative is \(\log(u/(1-u))+1/(1-u)\), so it still diverges at zero.

| [P] \(a\) | \(b\) | \(C\) | Loss coefficient | Supplied margin [U] | Remaining margin, approximately |
|---:|---:|---:|---:|---:|---:|
| 1.9 | 1.8999998 | 200 | 0.0000844444583 | 0.0002 | 0.000115555542 |
| 1.4 | 1.39998 | 200 | 0.0140004500160 | 0.031 | 0.016999549984 |
| 1.9 | 1.899989 | 8 | 0.000185779451 | 0.0002 | 0.000014220549 |
| 1.4 | 1.39890 | 8 | 0.030854556386 | 0.031 | 0.000145443614 |

**[P]** For exact rational endpoints even \(\log x\le x-1\) gives the first two strict bounds \(<0.000085\) and \(<0.01401\). Hence both weaker strict margins in (14), 0.00011 and 0.016, follow *given* the respective supply inputs. The conservative break-even exponent for \(C=8\) is \(b=1/(1-t_a e^{-c_a/(8a^2)})\), about 1.8999881580 and 1.3988948240. A strictly larger \(b\) leaves positive margin. **[I]** The constant matters for the size of a fixed improvement. Every positive fixed coefficient still exhausts finite supply as \(b\downarrow1\). The divergence concerns this loss estimate; it cannot establish that the genuine \(D_{1,1}\) is zero.

## [P] The local normalization and the synthetic lower bound

**[Q]** The [model definition](../../proof/strong_goldbach_research.md) is \(a_m^+=K_0^{-1}\mathbf1_{(m,N)=1}\prod_{\ell\mid m}(1+h(\ell))(1+\lambda(m))\), with \(h(\ell)=1/(\ell-2)\) on primes outside even \(N\) and \(K_0=(\varphi(N)/N)\prod_{\ell\nmid N}(1+h(\ell)/\ell)\).

| [P] Prime | Factor in \(K_0^{-1}\) | Factor in \(S\) |
|---|---:|---:|
| \(2\mid N\) | \(2\) | \(2\) |
| odd \(\ell\nmid N\) | \(\ell(\ell-2)/(\ell-1)^2\) | \(1-1/(\ell-1)^2\) |
| odd \(\ell\mid N\) | \(\ell/(\ell-1)\) | \((1-1/(\ell-1)^2)(\ell-1)/(\ell-2)\) |

**[P]** This proves \(K_0^{-1}=S\) term by term. Coprime semiprimes have \(a_m^+\ge2S\), while primes have zero mass. For an *unweighted* count the synthetic mass used for comparison is \(a_m^+/L\). For \(N^{1/4}<r\le N^{7/25}\), \(N/(2r)<q\le N/r\) both prime, \(q>r\) eventually and \(m=rq\) determines the pair uniquely. Both factors exceed \(N^{2/9}\). The strict margin \(7/25<t_{1.39998}\) ensures \(r\le q^{b-1}\) uniformly even at the lower endpoint of the \(q\)-interval, for both original narrowed exponents. It holds also at the two new example exponents.

**[P]** The PNT gives uniformly \((1+o(1))N/(2r\log(N/r))\) choices of \(q\), since \(N/r\ge N^{18/25}\to\infty\). Dropping \(r\mid N\) costs \(O(N^{-1/4}\log N)\) in the reciprocal-prime sum; dropping \(q\mid N\) costs \(O(N^{7/25}\log N)\) pairs. Weighted prime partial summation, followed by the lower bound \(2S/L\) per pair, gives mass in units \(SN/L^2\) at least
\[
 \int_{1/4}^{7/25}\frac{du}{u(1-u)}-o(1)
 =\log(7/6)-o(1)=0.1541506798\ldots-o(1).
\]
This exceeds both claimed baselines even on the intersection with the original rough set. No primality of the reflected coordinate \(N-m\) is imposed in this comparison.

**[P]** There is an additional endpoint test on the *unrestricted* synthetic candidates. For fixed \(1<b<a<2\), choose any interior interval \([u_0,u_1]\subset(t_b,t_a)\), use \(r\) between \(N^{u_0}\) and \(N^{u_1}\) and the same \(q\)-interval. Every resulting pair lies in the lost band for all sufficiently large \(N\). Letting the fixed interior endpoints approach the band edges shows the normalized model loss has liminf at least \(\int_{t_b}^{t_a}du/[u(1-u)]=\log((a-1)/(b-1))\). Thus a real logarithmic loss can occur in a sequence meeting the cited multiplicative tests under their hypotheses. For any *fixed* \(b>1\), an interior interval in \((0,t_b)\) likewise gives positive semiprime supply. The threshold can depend on \(b\). Keeping the extra cutoff \(r>N^{2/9}\) would require \(t_b>2/9\); the shrinking bands near 1 do not satisfy that requirement. **[I]** An endpoint theorem needs a new uniform estimate or a sign input. Passing to the limit in fixed-\(b\) positivity does not give one.

## [P] The two one-sided reductions

**[P]** For (8), set \(z=N^{2/9}\) and sum \(\log p\) over \(p<N,\ p\nmid N,\ m=N-p>1,\ P^-(m)>z\). Write \(S_z\) for that mass and \(H\) for the same sum with factor \(\lambda(m)+(1-\lambda(m))J_N(m)\), where \(J_N\) counts *distinct* prime divisors \(z<r,\ r^3\le N\). With \(m<N=z^{9/2}<z^5\), at most four prime factors with multiplicity can survive. Even \(\Omega\) gives zero on the left below. A prime gives at most two, including when that prime itself is marked. An odd composite has three factors, so its least prime \(r\) satisfies \(z<r,\ r^3\le m<N\). It contributes at most zero. Thus
\[
 (1-\lambda(m))(1-J_N(m))\le 2\mathbf1_{\mathbb P}(m),
 \qquad S_z-H\le2\sum_{p+q=N}\log p .
\]

**[P]** With Dirichlet GRH, the progression estimate for \(\sum\log p\) is \(N/\varphi(d)+O(\sqrt N L^2)\) for squarefree \(d\le\sqrt N\) coprime to \(N\). Omitting \(p\mid N,\ m=1\) costs \(O(L)\) per test. With \(D=\sqrt N/L^{10}\) the summed absolute error is \(O(N/L^8)\). The dimension-one product \(V_N(z)=\prod_{\ell\le z,\,\ell\nmid N}(1-1/(\ell-1))\) omits 2. Its inverse over intervals satisfies the usual dimension bound by the corresponding odd-prime product, and \(V_N(z)\gg1/\log z\). The lower linear sieve, using \(s\to9/4\), therefore gives \(S_z\ge(f_*-o(1))NV_N(z)\) with \(f_*=2e^\gamma\log(s-1)/s\) evaluated at \(s=9/4\), namely \(0.353275399553884\ldots\). If \(H\le(f_*-\epsilon)NV_N(z)\), the sieve error is below \(\epsilon/2\) eventually, giving (8) with coefficient \(\epsilon/4\). **[U]** The uniform bound on this particular \(H\) is missing.

**[P]** For (9), the set \(\mathcal C_N\) comprises prime \(p<N\) with \(m>1\) prime or a product of *two distinct* primes. No \(p\nmid N\) restriction is imposed here. Write \(G\) for the ordered prime-pair count, \(T\) for the candidate set size and \(B\) for its Möbius sum. For each of \(\mathcal C_N,D_{1,1.9},D_{1,1.4}\), if \(U\) counts its distinct semiprime complements, \(T=G+U,\ B=U-G,\ (T-B)/2=G\) exactly. Quantitative Chen supplies a lower bound \(\gg SN/L^2\) before removing prime squares. Their removal costs at most \(\sqrt N\), giving \(T\ge cSN/L^2\) for some absolute \(c>0\) eventually. Substitution gives (9). **[U]** The audit supplies neither a numerical \(c,N_0\) for Chen nor a genuine uniform strict bound \(B_C<cSN/L^2\). For the reported Li–Liu sets quantitative supply remains [U].

## [P] Every even target through 500,000

**[P]** Run `/tmp/astra_b015/venv/bin/python /tmp/astra_b015/sieve_audit.py --csv /tmp/astra_b015/all_even.csv`. The script requires Python and NumPy (run with Python 3.13.14 and NumPy 2.5.5). A smallest-prime-factor sieve constructs \(\Omega\), the prime indicator, and the three squarefree semiprime indicators. The tests \(r^{10}\le q^9\) and \(r^5\le q^2\) use Python integers. Counts for Chen and both \(D\) sets use integer convolution over \(\mathbf F_{998244353}\); each true coefficient is at most 500,000 and the transform length exceeds twice the cutoff. For \(S_z,H\) the code splits the range at exact changes to \(r^9\le N^2\) and \(r^3\le N\), convolves against \(\log p\) in floating point and subtracts the terms with \(p\mid N\). Each \(V_N\) uses its own factors. Direct trial division and direct log sums provide a separate check on 149 targets, including all seven threshold exceptions. The CSV retains counts, signed sums and ratios for every target; the log sums are numerical.

| [P] \(N\) | \(S_z\) | \(H\) | \(H/(NV_N)\) | \((\lvert\mathcal C\rvert,B_C)\) | \((D_{1,1.9},B_{1.9})\) | \((D_{1,1.4},B_{1.4})\) |
|---:|---:|---:|---:|---:|---:|---:|
| 10,000 | 4,128.53 | 229.99 | 0.055199 | (762, 254) | (742, 234) | (549, 41) |
| 100,000 | 37,436.49 | 8,015.29 | 0.213741 | (5,028, 1,788) | (4,868, 1,628) | (3,720, 480) |
| 300,000 | 205,667.79 | 49,701.08 | 0.240975 | (19,858, 4,198) | (19,072, 3,412) | (13,158, −2,502) |
| 500,000 | 160,513.94 | 31,899.39 | 0.197970 | (19,836, 7,628) | (19,248, 7,040) | (14,775, 2,567) |

**[P]** Of 249,999 even targets, \(H\) exceeded \(10^{-7}\) at 244,164 and was below \(-10^{-7}\) at 5,833. The two near-zero values occur at 4 and 6 (empty rough sums). Seven targets exceeded \(f_*\) after normalization: 62, 122, 128, 134, 136, 1,112 and 1,238. For \(100,000\le N\le500,000\), the maximum ratio was 0.2848857100 at 323,804, about 0.06839 below \(f_*\). These finite thresholds do not test the asymptotic sieve error. In the synthetic model the mass vanishes wherever \(\lambda=-1\), so \(H^+=S_z^+\) exactly for *any* mark, and \(B^+/T^+=1\) on every positive-mass squarefree Chen or narrowed set.

| [P] Even \(N\) interval | Median \(B_C/\lvert\mathcal C\rvert\) | Median \(B_{1.9}/D_{1,1.9}\) | Median \(B_{1.4}/D_{1,1.4}\) |
|---|---:|---:|---:|
| 10,000–99,998 | 0.350943 | 0.332185 | 0.137125 |
| 100,000–499,998 | 0.392783 | 0.374685 | 0.189971 |
| 400,000–500,000 | 0.402314 | 0.384374 | 0.205263 |

**[P]** In the last interval the ranges were \([0.049376,0.472400]\), \([0.004508,0.457513]\) and \([-0.577033,0.301816]\), respectively (rounded). The source normalized \(B_C\) by \(SN/L^2\) in (9); the fractions here use the measured set sizes as requested. For fixed \(N\), \(B/T=1-2G/T\) falls under narrowing when \(T\) decreases and \(G>0\). The medians depend on the chosen interval and the narrower bias can change sign. **[I]** These data distinguish genuine complements from the plus model within the range tested. They give no limiting bias or effective threshold beyond it.

## [P] What automorphic RH tests in (7)

**[Q,U]** Fix a tempered cuspidal \(\pi\) of fixed degree, its normalized standard coefficients \(A(p^j)\) and a *fixed* smooth \(V\) compactly supported in \((0,1)\). Use the usual analytic continuation, fixed-\(\pi\) zero-free half-plane under automorphic RH and polynomial vertical bounds for the reciprocal at positive distance to the critical line, with the stated local bounds at ramified primes. These analytic hypotheses are explicit. The algebra below does not verify RH. The report's wider setting also grants conductor-aspect estimates; no conductor-uniform family estimate is obtained in this deduction.

**[P]** For squarefree \((d,N)=1\), the sign difference is \(2K_0^{-1}\lambda(d)w(d)\) times a smoothed sum over \(m\), \(n=dm\), on the scale \(Y=N/d\). At a good \(p\nmid Nd\), put \(t=p^{-s}\), \(A_1=A(p)\). The signed local factor is \(1-(1+h(p))A_1t+O_{r,\eta}(|t|^2)\); the standard \(L_p(s,\pi)\) is \(1+A_1t+O_{r,\eta}(|t|^2)\). Their product has linear coefficient exactly \(-h(p)A_1\). Temperedness gives \(|A(p^j)|\le {j+r-1\choose r-1}\), so both tails are bounded uniformly for \(\Re s\ge 1/2+\eta\). Thus the residual factors have absolutely summable deviations \(O_{r,\eta}(h(p)|t|+|t|^2)\). At \(p\mid N\) the pre-multiplication factor is 1; at \(p\mid d\) it is \(\sum_{j\ge0}(-1)^j A(p^{j+1})t^j\). Its constant can vanish, so no division by \(A(p)\) is justified or needed. Bounded exceptional factors cost \(C^{\omega(Nd)}\ll_\epsilon (Nd)^\epsilon\). The normalizations \(w(d),K_0^{-1}\) likewise cost \(O_\epsilon(N^\epsilon)\).

**[P, conditional on the preceding hypotheses]** Dividing the resulting convergent residual product by \(L(s,\pi)\), Mellin inversion can shift to \(1/2+\eta\); the transform of \(V\) decays rapidly. Using smaller auxiliary epsilons gives \(O_{\pi,V,\eta}(N^\eta (N/d)^{1/2+\eta})\). For the unsigned reference weight the local linear coefficient is \(+(1+h)A_1\) and multiplication by \(1/L_p\) cancels \(+A_1\). Its series is \(L(s,\pi)\) times another convergent product. Entireness for cuspidal degree at least two allows the same shift and gives individual bounds for both signs. The trivial degree-one representation can have an unsigned main term. Summing the difference bound for \(d\le N^{1-\delta}\) costs \(O(N^{1-\delta/2+O(\eta)})\) for fixed \(\delta>0\) and small \(\eta\).

**[I]** The tested coefficient is multiplicative in \(n\). The constants may depend on every fixed \(\pi,V\) in a prescribed finite list. The argument gives no uniformity for a growing family or for changing tests chosen after seeing \(N\). A coefficient such as \(\Lambda(N-n)\), a Frobenius class at the reflected prime, or an off-diagonal pair \(\Lambda(N-dk)\Lambda(N-ek)\) is outside this Euler product. Agreement of the synthetic signs on the tested functionals cannot transfer a sign bound to a genuine shifted-prime sequence. It also cannot establish any independence of Goldbach from Grand RH.

## [P] Which changes of weight help

**[P]** Set \(z=N^\beta\) and let \(D=N^{\theta-o(1)}\) be the available divisor level. A positive lower linear-sieve baseline requires \(s=\theta/\beta>2\). For the GRH absolute remainder one has \(\theta=1/2\), hence \(\beta<1/4\); the cube-root cutoff has zero lower-sieve coefficient there. For \(1/5\le\beta<1/4\) every rough \(m<N\) has at most four factors. In fact *the inequality itself* works for every \(\beta>0\): any composite of odd \(\Omega\) has at least three factors, hence its least prime satisfies \(r^3\le m\). Moving the cutoff changes the mass and the marked sums, without forcing their sign. Even a level high enough for a cube-root lower baseline allows both prime and semiprime complements.

**[P]** Let \(G_R\) be the true log-weighted prime mass inside the rough sum. For any nonnegative mark \(J\) covering each odd composite with weight at least 1, the exact slack in the pointwise estimate sums to
\[
 H_J-(S_z-2G_R)
 =2\sum_{\substack{R\\m\ {\rm prime}}}(\log p)J(m)
 +2\sum_{\substack{R\\m\ {\rm composite}\\\Omega(m)\ {\rm odd}}}(\log p)(J(m)-1).
\]
The mark \(J_m=\#\{r\mid m:r\ {\rm prime},\,z<r,\,r^3\le m\}\) never charges a prime and is termwise at most \(J_N\). Capping it at one makes both slack sums vanish exactly. This improves the combinatorial bound to equality. Estimating \(S_z-H_{\min(1,J_m)}\) from below is then exactly estimating \(2G_R\) from below. The modified mark depends on \(m\), and one cannot transfer a bound for a linear progression remainder to that statistic.

**[P]** In \(a^+\) every positive-mass \(m\) has \(\lambda(m)=1\). Thus every expression \(H_J^+\) above equals \(S_z^+\), for any cutoff, mark or cap. On the squarefree Chen or narrowed sets any nonnegative reweighting of that model gives \(B^+=T^+\). In particular a strict fractional saving in \(B/T\) would exclude it. Given the model's normalized unsigned divisor masses \(N/\varphi(d)\) with the conditional errors in the source, a standard lower sieve at the above level also supplies the rough baseline for the model (the model at \(m=1\) costs only \(O_\epsilon(N^\epsilon)\)). Changing weights using only inputs shared by this model cannot force positive prime mass. **[I]** A switched estimate may still work if it uses a genuine two-form input that the model fails. Examples of sufficient inputs are a target-uniform upper bound on the marked signed sum with the stated \(f_*-\epsilon\) margin, or \(B_C\le(1-\epsilon)|\mathcal C_N|\) with independent Chen supply. A rearrangement of known unsigned divisor masses, including a nonnegative Selberg or Maynard weight, supplies no such distinguishing estimate here. This is a limit of the specified tests and deductions; the audit gives no universal impossibility theorem for future switched sieves.

**[Q,U]** The repository attributes a fixed-shift Möbius theorem and specific auxiliary subpower factor intervals to Lü–Wang–Wu. The paper and the Li–Liu paper have not been independently verified for this audit. **[P]** If a weight requires a divisor in an interval with upper endpoint \(N^{o(1)}\), it vanishes on \(N^\beta\)-rough \(m\) for any fixed \(\beta>0\) eventually. If three disjoint such prime intervals are required, no Chen complement qualifies. Two restrict eligible Chen complements to \(N^{o(1)}\); one on \(m\asymp N\) can select only a semiprime in the squarefree Chen set. Even an unrestricted \(o(N/\log N)\) estimate would allow a bias on the \(N/\log^2 N\) scale, with compensation outside the selected set. The stated support and scale issues survive the arbitrary choice of fixed automorphic tests.

## [P] Proposed Lean micro-lemma and direct verification

**[P]** The source uses \(r^3\le N\). The requested candidate uses the sharper \(r^3\le m\). On rough \(m<N\) the sharper inequality implies the source inequality because \(1-\lambda(m)\ge0\). The bound \(m<z^5\) is strictly weaker than \(m^2<z^9\) for \(z>1\). A real \(z\) permits the exact value \(N^{2/9}\) without flooring it. The following is the scratch Lean 4 declaration and proof.

```lean
import Mathlib

namespace B015

noncomputable def marked (z : ℝ) (m : ℕ) : ℕ := by
  classical
  exact (m.primeFactors.filter (fun r : ℕ => z < (r : ℝ) ∧ r ^ 3 ≤ m)).card

def liouville (m : ℕ) : ℤ :=
  if m = 0 then 0 else (-1 : ℤ) ^ m.primeFactorsList.length

theorem subcritical_marked_divisor (m : ℕ) (z : ℝ)
    (hz : 1 ≤ z) (hm : 1 < m) (hsize : (m : ℝ) < z ^ 5)
    (hrough : ∀ r : ℕ, r.Prime → r ∣ m → z < (r : ℝ)) :
    (1 - liouville m) * (1 - (marked z m : ℤ)) ≤
      if m.Prime then (2 : ℤ) else 0 := by
  classical
  have hm0 : m ≠ 0 := by omega
  have hmin := Nat.minFac_prime (show m ≠ 1 by omega)
  have hdiv := Nat.minFac_dvd m
  have hzmin := hrough _ hmin hdiv
  have hprod : m.minFac ^ m.primeFactorsList.length ≤ m := by
    calc
      _ ≤ m.primeFactorsList.prod := List.pow_card_le_prod _ _ (fun p hp =>
        Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactorsList hp).two_le
          (Nat.dvd_of_mem_primeFactorsList hp))
      _ = m := Nat.prod_primeFactorsList hm0
  have hlen : m.primeFactorsList.length ≤ 4 := by
    by_contra! h
    have h5 := (Nat.pow_le_pow_right hmin.pos (show 5 ≤ m.primeFactorsList.length by omega)).trans hprod
    have h5r : (m.minFac : ℝ) ^ 5 ≤ m := by exact_mod_cast h5
    have := pow_le_pow_left₀ (by linarith : 0 ≤ z) hzmin.le 5
    linarith
  have hnonzero : m.primeFactorsList.length ≠ 0 := by
    intro he
    have he' : m.primeFactorsList = [] := by simpa using he
    have := Nat.prod_primeFactorsList hm0
    simp [he'] at this
    omega
  have hmark : 0 ≤ (marked z m : ℤ) := by positivity
  by_cases hp : m.Prime
  · simp [hp, liouville, hm0, Nat.primeFactorsList_prime hp]
  · rw [if_neg hp]
    have hnot1 : m.primeFactorsList.length ≠ 1 :=
      fun h => hp (ArithmeticFunction.cardFactors_eq_one_iff_prime.mp h)
    have hcase : m.primeFactorsList.length = 2 ∨
        m.primeFactorsList.length = 3 ∨ m.primeFactorsList.length = 4 := by omega
    rcases hcase with h | h | h
    · norm_num [liouville, hm0, h]
    · have hcube : m.minFac ^ 3 ≤ m := by simpa [h] using hprod
      have hmem := (Nat.mem_primeFactors.mpr ⟨hmin, hdiv, hm0⟩)
      have hpos : 0 < marked z m := Finset.card_pos.mpr
        ⟨m.minFac, Finset.mem_filter.mpr ⟨hmem, hzmin, hcube⟩⟩
      norm_num [liouville, hm0, h]
      omega
    · norm_num [liouville, hm0, h]

end B015
```

| [P] Form of the rough complement | Reason the inequality holds |
|---|---|
| Prime, whether below, at or above the scale \(z^3\) | The only divisor prime is \(m\) and \(m^3>m\), so the sharper mark is zero and the left side equals 2. The original mark counts the prime when \(m^3\le N\), reducing the left side to zero. |
| \(pq\), including \(p^2\) | Even multiplicity count gives \(\lambda=1\) and left side zero. |
| \(p^3\) | \(p^3=m\) is included at equality. The sharper mark is exactly one. |
| \(pqr\), \(p^2q\) or \(pq^2\) | The smallest of the three factors has cube at most the product. It contributes one distinct mark even if repeated. Additional distinct marks only decrease the left side. |
| Four factors, with any coincidences | Even multiplicity count gives zero regardless of the mark. |

**[P]** The proof bounds the length of the factor list using \(\operatorname{minFac}(m)^{\Omega(m)}\le m\). Five factors contradict \(m<z^5\). For the only odd composite case the same inequality supplies the marked least factor. The prime and even cases then reduce to integer arithmetic. The scratch declaration elaborated with Lean 4.16.0 and its cached Mathlib. The separate dependency query printed `'B015.subcritical_marked_divisor' depends on axioms: [propext, Classical.choice, Quot.sound]`. The theorem source contains none of the prohibited proof tokens. It is a **proposed micro-lemma** without a repository strict-check acceptance. The blocker is the missing target-uniform analytic estimate. A machine proof of the factor inequality alone does not establish that estimate.

**[P]** The [experiment](/tmp/astra_b015/sieve_audit.py), [full output](/tmp/astra_b015/results.txt), [all-target CSV](/tmp/astra_b015/all_even.csv), [Lean source](/tmp/astra_b015/marked.lean) and [dependency output](/tmp/astra_b015/lean-audit.txt) are scratch files. The derivations, representative numerical results and Lean proof above are retained in this audit.

# Cross-modulus cancellation in the ultra-low Dirichlet zero sum

[Q] Wave 5, Strike 1C, 27 November 2026. Throughout, ERH means the Dirichlet hypothesis for every primitive character, including the character of conductor one. Tags denote a sourced input or observed computation [Q], a mathematical derivation [P], an interpretation [I], and an unresolved assertion [U]. The derivations below have no Lean verdict. The input for the Goldbach implication is the [Wave 4 report, §§5–6, equations (12)–(14)](B011_B002_W4_DECISIVE_LOWZERO_PUSH.md).

[P] **At Farey order \(N^{2/3}\), the reverse formula singles out a resonance.** Its zero frequency equals the exponentially weighted ordered von Mangoldt Goldbach coefficient times \(1+O(\log^{-4}N)\). The sum of *all nonzero frequencies* is \(-N\mathfrak S(N)/e+O(N/\sqrt{\log N})\) under the Wave 4 reduction. Thus asking for \(o(N)\) for those frequencies would give a false estimate. The lower bound still requires information about the resonant prime pairs. See equations 6–8.

[Q] At the three finite targets \(128,160,192\), the signed losses within moduli are larger than the additional losses across moduli. The ratio after summing the moduli ranges from \(0.226\) to \(0.752\); the ratio after summing the surviving character pairs within moduli ranges from \(0.154\) to \(0.201\). [U] Their ordering for large even targets is unknown.

## 1. Finite experiment with complete critical-line zero lists

[P] Put \(L=\log N, Q=\lfloor(N^2)^{1/3}\rfloor, D=Q/L^4, T=2\log L, K=L^2\). Fix the permissible \(\delta=1/4\) for all experiments. Retain precisely \(D<q\le Q, q\nmid N, h(q)\le L^8\), where \(h(q)\) is the product of the full prime powers of exponent at least two. For each unit \(a\), let \(r_\pm\) be the representatives of \(\pm a^{-1}\pmod q\) in \((Q-q,Q]\), and put \(w_a=1/[q(q+r_+)]+1/[q(q+r_-)]\). With \(e(x)=\exp(2\pi i x)\), set
\[
 b_\psi=\sum_{|t|<T}\Gamma(1/2+it)e^{itL},\quad
 v_j=\frac{\tau_q(\bar\chi_j)}{\varphi(q)}b_{\chi_j^*},\quad
 H_i=\sum_a^*w_a\chi_i(a)e(-Na/q).
\]
[P] Here and below the zero sum includes multiplicities. Conrey labels multiply in the character group. Use \(d_j=\operatorname{cond}(\chi_j)\ge q/K\). Drop the identically zero Gauss coefficient if \(q/d_j\) is nonsquarefree or shares a prime with \(d_j\). In the following primed sum, \(j\ne k\) and \((\operatorname{cond}(\chi_j\chi_k))^4>Q\). All surviving **ordered** pairs retain their original coefficients.
\[
 p_q=\Re\sum_{j,k}'H_{jk}v_jv_k,\quad
 A=\sum_q|p_q|,\quad
 J=\sum_q\sum_{j,k}'|H_{jk}v_jv_k|.                     \tag{1}
\]
[P] Wave 4 defines scalar \(b_\psi\). To specify the vector norm at each modulus, set \(b_q=\sqrt{\varphi(q)\max_a w_a}\,(v_j)_j\) and \(B=\sum_q\|b_q\|_2^2\). This is the unitary operator budget in the same normalization as \(p_q\). \(U_{aj}=\chi_j(a)/\sqrt{\varphi(q)}\) is unitary and the unmasked matrix \(U^{\mathsf T}\operatorname{diag}(w_a e(-Na/q))U\) has largest singular value \(\max w_a\). Pair masking changes the matrix. \(B\) is a reference budget for its input, with no contraction assumption on the masked matrix. Also report the literal unscaled input norm \(B_{\rm raw}=\sum_{q,j}|v_j|^2\). The ratio \(A/J\) directly tests cancellation among the surviving entries without assigning any gain from the deletions to cancellation.

[Q] The following computed enclosures are displayed as midpoints rounded with absolute error below \(2\cdot10^{-9}\) in every entry. The quotients in equation 1 define the exact ratios. Full Arb intervals are in the three summary files in the reproduction directory.

| \(N\) | \(Q\) | \(\sum p_q\) | \(A\) | \(B\) | \(B_{\rm raw}\) | \(J\) |
|---:|---:|---:|---:|---:|---:|---:|
| 128 | 25 | −0.00579636131 | 0.01112291610 | 0.07284954710 | 1.2631825390 | 0.05532183035 |
| 160 | 29 | +0.00952637989 | 0.01266671051 | 0.09313663162 | 2.0051045600 | 0.07884301381 |
| 192 | 33 | −0.00391698299 | 0.01734720210 | 0.11047428346 | 2.6014793684 | 0.11252497519 |

| \(N\) | Across moduli \(\lvert\sum p_q\rvert/A\) | Within moduli \(A/B\) | \(A/B_{\rm raw}\) | Surviving pair ratio \(A/J\) |
|---:|---:|---:|---:|---:|
| 128 | 0.521118856 | 0.152683394 | 0.00880547012 | 0.201058353 |
| 160 | 0.752080020 | 0.136001381 | 0.00631723191 | 0.160657361 |
| 192 | 0.225799121 | 0.157024799 | 0.00666820668 | 0.154163128 |

[I] Thus the larger multiplicative reduction occurs before the sum over \(q\) on these samples, even using the stricter comparison \(A/J\). The additional cross-modulus cancellation at 192 removes about 77% of what survives. This is an aggregate comparison. Some denominators have an empty or vanishing pair sum.

[Q] Per-modulus contributions and their running totals follow. **Every entry in this table is multiplied by 1,000.** A dash means the modulus was excluded. Rows excluded at all three targets are omitted.

| \(q\) | 128 | cumulative | 160 | cumulative | 192 | cumulative |
|---:|---:|---:|---:|---:|---:|---:|
| 3 | 0.000000 | 0.000000 | 0.000000 | 0.000000 | — | — |
| 5 | 0.000000 | 0.000000 | — | — | 0.000000 | 0.000000 |
| 6 | 0.000000 | 0.000000 | 0.000000 | 0.000000 | — | — |
| 7 | 0.000000 | 0.000000 | 0.000000 | 0.000000 | 0.000000 | 0.000000 |
| 9 | 0.000000 | 0.000000 | 0.000000 | 0.000000 | 0.000000 | 0.000000 |
| 10 | 0.000000 | 0.000000 | — | — | 0.000000 | 0.000000 |
| 11 | -0.252787 | -0.252787 | 0.384367 | 0.384367 | 0.200172 | 0.200172 |
| 12 | 0.000000 | -0.252787 | 0.000000 | 0.384367 | — | — |
| 13 | -0.031703 | -0.284490 | 0.768028 | 1.152395 | -0.113333 | 0.086840 |
| 14 | 0.000000 | -0.284490 | 0.000000 | 1.152395 | 0.000000 | 0.086840 |
| 15 | 0.005032 | -0.279458 | -0.000003 | 1.152392 | -0.009606 | 0.077234 |
| 17 | -4.582006 | -4.861465 | 1.294866 | 2.447258 | -0.988669 | -0.911435 |
| 18 | 0.000000 | -4.861465 | 0.000000 | 2.447258 | 0.000000 | -0.911435 |
| 19 | -3.482677 | -8.344142 | -1.263175 | 1.184083 | 2.857638 | 1.946203 |
| 20 | 0.001872 | -8.342269 | — | — | -0.067393 | 1.878810 |
| 21 | 0.087380 | -8.254890 | -0.045447 | 1.138636 | -0.065318 | 1.813492 |
| 22 | -0.110465 | -8.365355 | 0.155310 | 1.293945 | 0.088834 | 1.902326 |
| 23 | 1.775696 | -6.589659 | 5.798433 | 7.092379 | 3.213638 | 5.115964 |
| 24 | 0.012348 | -6.577310 | -0.000644 | 7.091735 | — | — |
| 25 | 0.780949 | -5.796361 | 0.214516 | 7.306251 | -0.640214 | 4.475751 |
| 26 | — | — | 0.341109 | 7.647360 | -0.032719 | 4.443032 |
| 27 | — | — | -0.260896 | 7.386464 | -1.256165 | 3.186867 |
| 28 | — | — | 0.763458 | 8.149922 | 0.354827 | 3.541694 |
| 29 | — | — | 1.376458 | 9.526380 | -4.223623 | -0.681929 |
| 30 | — | — | — | — | -0.004547 | -0.686476 |
| 31 | — | — | — | — | -1.744162 | -2.430637 |
| 33 | — | — | — | — | -1.486346 | -3.916983 |

### Root counting and arithmetic verification

[P] The root isolator works on the full signed interval \([-4,4]\), which contains each requested band. For a primitive nonprincipal character of parity \(\epsilon\), it uses the real Hardy function multiplied by the positive factor \((d/\pi)^{(1/2+\epsilon)/2}|\Gamma((1/2+\epsilon+it)/2)|\). This is the completed \(L\)-function on the line up to a constant phase. A rigorous, simple bound for its second derivative comes from the split theta integral. Mellin-transform \(\sum_{n\ge1}n^\epsilon\chi(n)e^{-\pi n^2x/d}\) and use the primitive theta functional equation on \(0<x<1\). The resulting two integrals on \([1,\infty)\) have powers \(x^{(s+\epsilon)/2-1}\) and \(x^{(1-s+\epsilon)/2-1}\), conjugate characters and a unit root number. Both absolute powers are at most one at \(\Re s=1/2\). Exponential convergence permits two differentiations. Each costs \((\log x)^2/4\) after the second derivative. Since \(\log^2 x\le x\), a bound is
\[
 M_d=1+\tfrac12\sum_{n=1}^{d} n^\epsilon e^{-k_n}(k_n^{-1}+k_n^{-2}),
 \qquad k_n=\pi n^2/d .
\]
[P] For \(n>d\), \(k_n>\pi n\), and \(n^\epsilon(k_n^{-1}+k_n^{-2})/2<1\), so the added 1 covers the entire tail. On an interval of length \(u\), linear interpolation errs by at most \(M_du^2/8\). Same-sign endpoints of magnitudes exceeding this certify absence of zeros. If signs differ and the endpoint difference exceeds \(M_du^2/2\) in magnitude, the derivative has a fixed strict sign throughout: its distance from the secant slope is at most \(M_du/2\) by integrating the Lipschitz derivative. This certifies exactly one simple zero. The other intervals are bisected. Under ERH this counts the full nontrivial spectrum in the band. Conductor one uses the Arb zeta count at 4 and conjugation.

[Q] All endpoint tests passed at 90-bit Arb precision. Each isolated zero was bisected to width at most \(2^{-40}\); no interval touched a height cutoff. Reflections were used only to pass from a character to its conjugate. Primitive induction was identified by comparing the exact rational character arguments on every unit of \(q\). For each nonvanishing Gauss coefficient the computed squared Gauss sum contained \(d\). Reassembling the trimmed and omitted terms enclosed the direct center square at every \(q\); each trimmed imaginary part enclosed zero. Cell lengths were formed as exact fractions before evaluation. The denominator cutoff, the height and the powerful-part conditions were evaluated for the stated targets, independently of any asymptotic onset.

[Q] The scratch directory is [/tmp/astra_w5_1c](/tmp/astra_w5_1c). Run the following command to regenerate the complete zero lists, interval-valued per-modulus CSVs and summary intervals with the preinstalled Wave 2 environment. Cold replay took 3.726 seconds wall clock, including root isolation. Each numerical invocation has an eight-second timeout. The summaries list \(N,Q,\sum p_q,A,B,B_{\rm raw},E,J,B_{\rm signs},|\sum p_q|/A,A/B,A/B_{\rm raw},A/E,A/J\), where \(E=\sum_{q,a}w_a|\sum_jv_j\chi_j(a)|^2\) and \(B_{\rm signs}\) is defined in §4. [Root isolator](/tmp/astra_w5_1c/zeros.py) · [Quadratic form](/tmp/astra_w5_1c/anatomy.py) · [Replay script](/tmp/astra_w5_1c/replay.sh)

~~~sh
timeout 9 bash /tmp/astra_w5_1c/replay.sh
~~~

## 2. Reverse the explicit formula before applying a Kloosterman estimate

[P] Let \(w_n=\Lambda(n)e^{-n/N}\), \(S(x)=\sum_{n\ge1}w_ne(nx)\). Below, \(w_{q,a}\) denotes the cell length called \(w_a\) in §1. The primitive Mellin formula at the positive real point \(z=1/N\) gives
\[
 \sqrt N b_\psi={\bf1}_{d=1}N-\sum_{n\ge1} w_n\psi(n)
       +r_\psi-\sqrt N\,t_\psi,\qquad
 t_\psi=\sum_{|\gamma|\ge T}\Gamma(1/2+i\gamma)N^{i\gamma}.
                                                               \tag{2}
\]
[P] The term \(r_\psi\) contains the residue at zero and the shifted integral. Wave 4 §1 gives \(r_\psi\ll L^2\) uniformly for \(d\le Q\le N\) at this point. Equivalently, shift \(-\Gamma(s)(L'/L)(s,\psi)N^s\) from \(\Re s>1\) to \(-1/2\) with its pole at one for the principal primitive character. The gamma tail is absolutely convergent, and counting zeros per unit interval gives \(t_\psi\ll L e^{-\pi T/2}\) for \(T=2\log L\). Thus (2) implements the **sharp** spectral cut without a compactly supported Fourier-test approximation. The prime sum converges absolutely. All character and Farey sums are finite.

[P] Write \(\mathcal D\) for the retained denominators and use the center norm \(\|Y\|_w^2=\sum_{q\in\mathcal D,a}^*w_{q,a}|Y(q,a)|^2\). Here are the estimates that permit the exact masks of (1) to be opened before applying a theorem to arithmetic coefficients.

1. [P] Returning the diagonal and low-product-conductor entries costs \(O_\varepsilon(N^{1+\varepsilon}(1+Q^{1/2-\delta})/\sqrt Q)\) in the unnormalized statistic by the Wave 4 completed hybrid sum and Cauchy bound. On \(q=hs\) with \(h\le L^8\) powerful and \(s\) squarefree coprime to \(h\), its normalized kernel bound is \(N^\varepsilon\sqrt{q(q,N)}/(qQ)\). A fixed product or the whole diagonal has total coefficient weight \(O(L^2)\); the number of small products is at most \(Q^{1/2-\delta}\tau(q)\). The bound \(\sum_{q\le Q}\sqrt{(q,N)/q}\ll\sqrt Q\,\tau(N)\) accounts for moduli sharing factors with the target. Choose \(\varepsilon<\theta\delta/2\) for fixed \(Q\asymp N^\theta\).
2. [P] In the field multiplied by \(\sqrt N\), restoring the small inducing conductors costs \(O(\sqrt N L/K)\) in center norm. Indeed, with \(q=dr\) the nonzero induced coefficients require \((d,r)=1\), \(r\) squarefree, and have squared magnitude \(d/\varphi(q)^2\). Using \(w_{q,a}\le2/(qQ)\), character orthogonality, and \(|b_\psi|\ll L\), the squared cost divided by \(O(NL^2)\) is at most \(\sum_{r>K}1/(r^2\varphi(r))\ll K^{-2}\) by bounded mean of \(r/\varphi(r)\). Adding the high gamma tail costs \(O(\sqrt N L^{1-\pi})\) by the same orthogonality and \(\sum_j|c_j|^2=1\), where \(c_j=\tau_q(\bar\chi_j)/\varphi(q)\).
3. [P] In (2) replace \(\psi(n)=\chi^*(n)\) by \(\chi(n)\). Only powers of primes dividing \(q\) can change. Each such prime contributes \(O(L)\) in absolute weight by summing below \(N\) and the exponentially decreasing tail above it. Per character the error and \(r_\psi\) cost \(O(L^2)\). Their combined center norm is \(O(L^2)\), since \(\sum_q2\varphi(q)/(qQ)=O(1)\) and \(\sum_j|c_j|^2=1\). Now \(\sum_j c_j\chi_j(a)\chi_j(n)={\bf1}_{(n,q)=1}e(an/q)\) by character orthogonality. Restoring the nonunit prime powers also costs \(O(L^2)\) pointwise. The pole contributes \(N\mu(q)/\varphi(q)\), hence has center norm \(O(NQ^{-1}L^{O(1)})\) on \(q>D\).
4. [P] For \(1/2<\theta\le1\), the sampled prime field has norm \(O(\sqrt{NL})\). Indeed the center-to-cell constant approximation differs in \(L^2\) on these cells from the continuous field by at most \((\max w_{q,a})\|S'\|_2\), by Cauchy on each disjoint interval. Its width bound is \(2L^4/Q^2\). Parseval and Chebyshev give \(\|S\|_2\ll\sqrt{NL}\) and \(\|S'\|_2\ll N^{3/2}\sqrt L\). Thus the error of deleting or restoring all the field terms above is \(O(\sqrt N/L)\) for fixed \(\theta>1/2\). Cauchy on the difference of the two bilinear squares gives \(O(N/\sqrt L)\).

[P] Consequently, for the *center statistic* at any fixed \(1/2<\theta\le1\),
\[
 N\mathcal P_N^\circ
  =\Re\sum_{q\in\mathcal D,a}^* w_{q,a}e(-Na/q)\,S(a/q)^2
       +O_\theta(N/\sqrt L).                                  \tag{3}
\]
[P] The implicit constant can also depend on fixed \(\delta\). This generalization concerns the center statistic. The Wave 4 identification with the original H2 functional is invoked here only at \(2/3\). At \(\theta=1/2\) the pole budget in step 3 reaches the square-root power and step 4 loses logarithms. The ledger below at this endpoint is for the displayed prime kernel; (3) with a little-oh remainder is not asserted there.

[P] Set \(R_N(h)=\sum_{n+m=N+h}w_nw_m\) for \(n,m\ge1\), with value zero for an empty sum. Reorder the right side of (3) to obtain \(\sum_{h\in\mathbb Z}R_N(h)K_N(h)\), where
\[
 K_N(h)=\sum_{q\in\mathcal D,a}^*w_{q,a}e(ha/q)
  =\sum_{q\in\mathcal D}
     \sum_{\substack{Q-q<r\le Q\\(r,q)=1}}
       \frac{e(h\bar r/q)+e(-h\bar r/q)}{q(q+r)} .             \tag{4}
\]
[P] Switching \(a\) to \(r\) in each of the two half-lengths proves (4); in particular the sign and both endpoints matter. The kernel is real. Absolute summability follows from \(\sum_n w_n<\infty\) and \(\sum_{q,a}w_{q,a}\le1\). This puts the entire \(q\)-sum inside the prime convolution and yields actual untwisted Kloosterman fractions. Using such a bound on \(H_{jk}v_jv_k\) directly would require separating coefficients that still depend on the modulus.

[Q] A separate finite-polynomial check used \(w_n\) for \(n\le N\), exact fractional cell lengths, and ordinary double precision for the phases. At 128, 160 and 192, direct evaluation at Farey centers and convolution against the inverse-fraction kernel in (4) differed by less than \(6.2\cdot10^{-13}\) in the unnormalized sums. The zero-frequency weights agreed with the separately summed exact rational masses to \(10^{-13}\). [Independent kernel check](/tmp/astra_w5_1c/kernel_check.py)

## 3. The exponent ledger and the zero frequency

[Q] Pascadi's local manuscript gives a balanced bilinear bound for nonzero numerator \(h\), variables at most \(Q\), and separate \(\ell^2\) coefficients. Its saving relative to \(Q\|\alpha\|_2\|\beta\|_2\) is expressed by the factor \(Q^{-1/12}+|h|^{1/32}Q^{-1/8}+|h|^{1/2}Q^{-1}\), up to \(Q^{o(1)}\). The headline \(Q^{-1/12}\) factor alone requires \(|h|\ll Q^{4/3}\). The main trilinear theorem requires numerator length \(A\ll Q^{1/14}\), with factor \(Q^{-1/12}A^{-1/3}\) relative to the trivial \(\ell^2\) bound. Below we also use the *full-range* balanced trilinear corollary. These are quoted inputs from the supplied manuscript. [Bilinear theorem and hypotheses](/tmp/arxiv_nov2026/2611.34917v1/main.tex:50) · [Bilinear corollary](/tmp/arxiv_nov2026/2611.34917v1/main.tex:2919) · [Trilinear corollary](/tmp/arxiv_nov2026/2611.34917v1/main.tex:2970)

[P] The conditions on the sequences can be met in (4). The modulus restrictions depend only on \(q\). Expand \({\bf1}_{q+r>Q}\) in additive characters of \(q+r\) on a cyclic group of order \(4Q+1\), using the interval \((Q,2Q]\). Its normalized Fourier coefficients have total absolute sum \(O(\log(2Q))\) by the finite geometric sum. Represent \(1/(q+r)=\int_0^\infty e^{-uq}e^{-ur}\,du\) and include \(1/q\) in the modulus coefficient. The two norms have product at most \(Q D^{-1}e^{-uD}\). Integration costs at most \(Q/D^2=Q^{-1}L^8\), including the \(1/q\). Coprimality is exactly the one in the theorem. Multiplying by the \(Q\) in the normalized bound leaves logarithms only. All separations have finite sums or an absolutely integrable majorant.

[P] Truncating \(n,m\le C N L\) for a sufficiently large fixed \(C\) costs \(O(N^{-10})\) by exponential decay and \(|K_N(h)|\le1\). For \(|h|=N^{1+o(1)}\), \(Q=N^{\theta+o(1)}\), the saving in the pointwise bound for (4) is \(N^{-s_B(\theta)+o(1)}\), where
\[
 s_B(\theta)=\min\{\theta/12,\ \theta/8-1/32,\ \theta-1/2\}.
                                                               \tag{5}
\]
[P] The three active intervals, in increasing order of \(\theta\), are \([1/2,15/28]\) (last term), \([15/28,3/4]\) (middle term), and \([3/4,1]\) (first term). Summing with \(\sum_h R_N(h)\ll N^2\) gives exponent \(2-s_B(\theta)\) for nonzero \(h\). At \(2/3\) this is \(187/96\). Substituting the headline bound for this range of \(h\) would misstate its conductor uniformity.

[P] For \(1\le |h|\asymp A=N^{\alpha+o(1)}\) the numerator coefficients are \(R_N(\pm h)\) on the indicated interval and zero elsewhere. The elementary bound \(\|\nu\|_2\ll N^{1+o(1)}\sqrt A\) follows by counting at most \(O(NL)\) summands of size \(O(L^2)\) per \(h\). Use the trilinear corollary with eigenvalue parameter \(7/64\), the quoted unconditional upper bound, and sum each sign separately. Relative to the baseline \(N^{1+\alpha+o(1)}\), its saving exponent is
\[
 s_T(\theta,\alpha)=\min\left\{
 \frac{\theta}{12}+\frac{\alpha}{3},\
 \frac{25\theta+79\alpha}{286},\
 \frac{3\theta}{28}+\frac{79\alpha}{700},\
 \theta-\frac{\alpha}{2}\right\}.
\]
[P] These terms follow by substituting \(7/64\) into the two middle powers of the corollary. Each of \(1+\alpha-s_i\) increases with \(\alpha\), so the worst dyadic range is \(\alpha=1\), allowing logarithms in the upper endpoint. The resulting exponent on \([1/2,1]\) is
\[
 2-\min\{\theta-1/2,\ 3\theta/28+79/700\}.
\]
[P] The transition is \(\theta=429/625\); the exponent at \(2/3\) is \(11/6\). The main trilinear theorem alone only covers \(\alpha\le\theta/14\). Neither ledger spends a saving on the zero numerator. A further check, independent of the manuscript, is dual additive large sieve: separation of distinct Farey centers by at least \(Q^{-2}\) gives \(\sum_{|h|\le A}|K_N(h)|^2\ll(A+Q^2)\sum w_{q,a}^2\ll(A+Q^2)L^4/Q^2\). This gives exponent \(3/2\) via Cauchy at \(A=N^{1+o(1)}\). The original sampled square has the stronger unsigned energy exponent \(1\) up to logarithms throughout \([1/2,1]\), by the additive large sieve on \(S\), \(\max w_{q,a}\ll L^4/Q^2\), and the same exponential truncation.

[P] At precisely \(h=0\) there is no inverse phase. All the Farey cells partition the circle, and the total mass for any one denominator is at most \(2/Q\). The three discarded sets \(q\le D\), \(q\mid N\), and \(h(q)>L^8\) contain \(O(Q/L^4+\tau(N))\) denominators in total. For the powerful part, sum \(Q/j\) over powerful \(j>L^8\), using \(\#\{j\le x:j\ {\rm powerful}\}\ll\sqrt x\). Hence, for the full range of \(\theta\),
\[
 K_N(0)=1+O(L^{-4}+\tau(N)/Q).
                                                               \tag{6}
\]
[P] At frequency zero, \(R_N(0)=e^{-1}\sum_{n+m=N}\Lambda(n)\Lambda(m)\ll NL^2\). It differs from the prime-only \(P_N\) by \(O(\sqrt N L^{O(1)})\): there are \(O(\sqrt N\log N)\) eligible integers \(p^k\), \(k\ge2\), and each fixes the other summand. Equations (3) and (6) now give at \(\theta=2/3\)
\[
 N\mathcal P_N^\circ=P_N+\sum_{h\ne0}R_N(h)K_N(h)+O(N/\sqrt L).
                                                               \tag{7}
\]
[P] Subtracting (7) from Wave 4 (14) in its trimmed form yields
\[
 \boxed{\displaystyle \sum_{h\ne0}R_N(h)K_N(h)
             =-\frac{N\mathfrak S(N)}{e}+O(N/\sqrt L).}        \tag{8}
\]
[P] Since \(\mathfrak S(N)>1.32032\) for even \(N\), the nonzero-frequency contribution has magnitude \(\gg N\) at every sufficiently large even target. Its power is exactly one, allowing \(N^{o(1)}\) for the target-dependent singular series (e.g. its Euler factors at primes dividing \(N\) are \(N^{o(1)}\)). This is a wall for an actual term in the reverse calculation. It also fixes its sign. Obtaining a better bound for a **centered discrepancy** around (8) would still leave the unknown \(R_N(0)\) in (7).

[P] An exponent-one wall for bounds using only input energies holds for *every* \(\theta\in[1/2,1]\). For a concrete signed example pick independent random signs \(a_n\) for \(1\le n<N/2\), put \(a_{N-n}=-a_n\), and set the other coefficients to zero. Then \(e(-Nx/2)\sum a_ne(nx)\) is purely imaginary. The real part of its squared phased sum is \(-|\sum a_ne(nx)|^2\). At a retained center \(a/q\), its expected squared magnitude is \(N-2+O(1/\|2a/q\|_{\mathbb R/\mathbb Z})\), by the geometric series for \(\sum_{n<N/2}e((2n-N)a/q)\). Here \(q>2\) for large \(N\). Multiplication by two has fibers of size at most two modulo \(q\), and \(2a\not\equiv0\), so summing the error over units costs \(O(q\log q)\). Weight by \(2/(qQ)\) and sum over \(q\): the expected signed result is \(-(N-2)K_N(0)+O(\log Q)\). Some bounded real sequence therefore attains a negative contribution of order \(N\) with squared input norm \(N-2\). Together with the large-sieve upper exponent this is sharp for that class, even for one-sided estimates. [I] The example has signed coefficients. Its role is to identify which arithmetic information an energy-only estimate discards. [U] General Kloosterman arguments retaining additional prime structure are not excluded by this calculation.

## 4. Which negative directions can a spectrum realize?

[P] The full unweighted center matrix is complex symmetric and unitary. Its singular values do not assign an ordinary \(-1\) eigenspace to the trimmed matrix. The actual lengths change the singular values, and deleting entries changes the quadratic form again. There is a direct test in the appropriate real space. For \(X_q(a)=\sum_jv_j\chi_j(a)\), conjugation of the zeros gives \(b_{\bar\psi}=\bar b_\psi\), and the Gauss coefficients give \(v_{\bar j}=\chi_j(-1)\bar v_j\). Thus \(X_q(-a)=\overline{X_q(a)}\). Put \(Y_q(a)=e(-Na/(2q))X_q(a)\), well defined on residues because \(N\) is even. Before pair deletion the signed statistic is *exactly*
\[
 \sum_{q,a}^*w_{q,a}\big((\Re Y_q(a))^2-(\Im Y_q(a))^2\big).
                                                               \tag{9}
\]
[P] A purely imaginary \(Y\) would give the negative of the full field energy. Whether the primitive spectral coordinates can produce it is a separate constraint. For any proposed ERH-line family with the same uniform unit-interval count bound, \(|b_\psi|\ll L\). Thus the sparse-pair deletion proof in §2 applies to it too. For such a family, reaching the adverse threshold requires the weighted imaginary-square energy to exceed the real-square energy by at least \(\mathfrak S(N)/e-o(1)\). The fields in this criterion carry the genuine induction relations between moduli. It suffices to control their *aggregate difference*; control of the absolute energy or of every modulus separately is stronger than the signed requirement.

**[P] Exact counting-function model on the measured conductors.** Specify \(N_\psi(u)=\#\{|\gamma|\le u\}\) for every \(u\) in the measured band and each primitive character, counting multiplicity. Preserving this function fixes its multiset of absolute ordinates. For a conjugate pair select signs once, reflect them for the partner, and use the same primitive list in every lift. For a real character its own spectrum must be reflection-invariant. In the complex case conjugation gives
\[
 g_N(-t)=\overline{g_N(t)},\qquad g_N(t)=\Gamma(1/2+it)e^{itL}.
\]
[P] In particular \(\Re b_\psi\) is fixed and \(\Im b_\psi\) is a finite signed sum with prescribed magnitudes. There is no freedom to assign independent unit phases. Every choice, even if sign and moment constraints are subsequently relaxed, satisfies the envelope
\[
 |\mathcal P_N^\circ|\le B_{\rm signs}
 =\sum_{q,j,k}' |H_{jk}|\,|c_jc_k|\,u_{j^*}u_{k^*},\qquad
 u_\psi=\sum_{|\gamma|<T}|\Gamma(1/2+i\gamma)|.
                                                               \tag{10}
\]
[Q] The respective upper endpoints from (10) are below \(0.060979,\ 0.092726,\ 0.139076\). Each is below \(1.32032/e>0.485\). Thus **no** assignment preserving these exact counts reaches the proposed negative threshold on **any** of the three targets, even before imposing low moments. To test a further low moment explicitly, the script checked every nonempty subset of the signed genuine ordinates of each contributing nonreal primitive character for each target. Every subset-sum ball excluded zero. Flipping that subset changes the first signed moment by minus twice its sum. Preserving the exact first signed moment therefore fixes all signs in these finite data. Reflection already fixes the real-character multiset. All even ordinate moments were fixed by the counts alone. [I] This test has no large-conductor extrapolation.

**[P] Coarse zero density and fixed moments allow phase motion.** A Riemann–von Mangoldt main term with an error allowance is weaker than equality of \(N_\psi(u)\) with a particular genuine function for every \(u\). Here is an explicit test of what finitely many ordinate moments can retain. Fix \(k\ge1\) and a nonreal conjugate-character pair. Take \(t_j=t_0+j\pi/L\), \(0\le j\le k+1\), multiplicities \(m_j=\binom{k+1}{j}\), and \(\sigma_j=(-1)^j\). Put the first spectrum at \(\sigma_jt_j\) and the second at \(-\sigma_jt_j\), with these multiplicities, on the critical line. In each construction use the reflected list for the conjugate character. Pick \(t_0=1+O(1/L)\) so \(e^{it_0L}\Gamma(1/2+i)\) is positive imaginary. Both lists are in the band for large \(N\). Their exact two-sided counts agree at every height and so do their even moments. For odd \(r\le k\) their moment difference is \(2\sum_j(-1)^jm_j t_j^r=0\) by the \((k+1)\)-st finite difference. Their \(b\)'s, however, differ by
\[
 2i\sum_j(-1)^jm_j\Im g_N(t_j)
   =2i\,2^{k+1}|\Gamma(1/2+i)|+O_k(1/L).
\]
[P] This follows from \(e^{it_jL}=(-1)^je^{it_0L}\) and bounded derivatives of \(\Gamma\) near \(1/2+i\). Adding the same background lists to both models preserves these equivalences and perturbs a background counting formula by at most \(2^{k+1}\) at every height. The construction permits multiplicities and concerns moments of *ordinates*. It demonstrates a missing phase constraint even with exactly matched counts **between the two synthetic lists**. [U] It does not match the measured genuine counting functions, impose the Euler product, or establish a simultaneous threshold-crossing example along unbounded \(N\).

**[P] A rigidity condition for genuine primitive spectra.** Equation (2) pins each \(b_\psi\), uniformly for the relevant primitive conductors, to the same arithmetic sequence of prime weights:
\[
 \left|b_\psi-\frac{{\bf1}_{d=1}N-\sum_n w_n\psi(n)}{\sqrt N}\right|
 \ll L^{1-\pi}+L^2/\sqrt N.                                   \tag{11}
\]
[P] Two assignments satisfying (11) with the *same prime coefficients* differ coordinatewise by \(O(L^{1-\pi}+L^2/\sqrt N)\). By center orthogonality and the length majorant, the norm \(\|X-X'\|_w\) of their dimensionless field difference is at most a constant times this quantity. Each field norm is \(O(L)\) under the unit-interval count bound. Cauchy on (9), followed by the sparse-pair bound for both assignments, gives a change \(O(L^{2-\pi}+L^3/\sqrt N)+o(1)=o(1)\) in the trimmed statistic. A model producing an order-one *change* through independent conductor phases must therefore violate this arithmetic compatibility or the stated counting conditions. Equality of a few low moments does not implement (11). [U] This rigidity obstructs free spectral alignment. The sign of the common genuine statistic still requires a pointwise arithmetic estimate.

[U] **Verdict.** B-011 and B-002 remain open under Dirichlet ERH. The measured spectra settle the within-versus-across comparison for the three reported targets. Equation (8) settles the scale and sign of the nonzero-frequency term in this particular reverse formula. Neither the finite sign test nor a general \(\ell^2\) Kloosterman bound yields the required asymptotic lower bound for \(\mathcal P_N^\circ\).

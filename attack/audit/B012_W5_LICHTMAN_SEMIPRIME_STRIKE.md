# A one-sided test on central semiprimes

**[P]** Lichtman’s exact partition assigns every semiprime to the exceptional set. For the three-von-Mangoldt sum in the brief, the optimal main term of the prime-row Selberg square at prime progression level \(\theta<1\), relative to Hardy–Littlewood, is
\[
  2+\frac{2(1-\theta)}{\delta}
        \log\frac{\theta-1/2+\delta}{\theta-1/2}.
\]
Its infimum over \(1/2<\theta<1\) is exactly 2. A direct Cauchy–Schwarz argument on the genuine primes instead has normalized diagonal \(o(1)\) and needs a normalized off-diagonal strictly below 4. **[U]** The cited Kloosterman estimates do not establish that bound. This leaves B-012 open, including under prime Elliott–Halberstam (EH). The calculation gives an obstruction for a specified majorant and an explicit target for a different calculation.

[Q] denotes a statement in a cited source, [P] a derivation or executed check, [I] an interpretation and [U] an unresolved input. No result here has a Lean verdict.

## 1. The support of Lichtman’s partition

[Q] Theorem 1.2, equation (1.5), of the cached v1 states \(\sum_{p\le x}\mu(p+2)\ll_\epsilon\pi(x)(\log x)^{-1/2+\epsilon}\). Theorem 1.1 concerns \(\mu(n)\mu(n+1)\) and has exponent \(1-\epsilon\). The text attributes the improvement over Lü–Wang–Wu’s qualitative \(o(\pi(x))\) to replacing averaged overlapping weights with a disjoint partition. Section 7 gives the detailed completion for Theorem 1.1. The corresponding shifted-prime adaptation is announced in the introduction. In particular the displayed completed-pattern and typical-integer results, Proposition 7.3 and Corollary 7.4, explicitly carry Möbius factors on both sides. Theorem 1.2 is quoted here as a source result. [Lichtman, introduction](/tmp/arxiv_nov2026/2611.28392v1/binary_chowla1.tex:105) · [Completed patterns](/tmp/arxiv_nov2026/2611.28392v1/binary_chowla1.tex:1138)

[Q] Write \(L=\log x\), \(0<\alpha<\beta<1/2\), \(\gamma=\beta-\alpha\). Equations (4.1)–(4.3) give \(B=\lfloor\gamma\log L/\log2\rfloor\) adjacent intervals \((e^{\lambda_j},e^{2\lambda_j}]\), \(\lambda_j=2^{j-1}L^\alpha\), and \(T(v)=\sum_J\phi_J(v)\). Each \(J\) records exactly the **first \(3k\) successful intervals** of \(v\). Every third selected interval is active, so their scales have ratio at least \(8>19/3\). The passive indicator is invariant under multiplication by an active prime, equation (4.4). Lemma 6.1, equations (6.4)–(6.5), extracts one divisor prime from each active interval with reciprocal multiplicity \(1/\prod_i(1+\omega_i(v/a))\) and sign \((-1)^k\). The identity for \(\mu(v)\phi(v)\) requires absence of active prime squares, and the total extraction weight is always at most one. [Partition](/tmp/arxiv_nov2026/2611.28392v1/binary_chowla1.tex:638) · [Ramaré identity](/tmp/arxiv_nov2026/2611.28392v1/binary_chowla1.tex:936)

[Q] After that extraction, equal cofactors \((mn+1)/a=(rs+1)/b\) give \(bmn-ars=a-b\). The common-prime terms are treated by Lemma 6.2. The determinant reduction adapted from the Poisson–Dirichlet work lifts the endpoints to primitive vectors, with determinant divided by the auxiliary list product equal to \(bmn-ars\). The major arcs exploit a rough Möbius coefficient (Propositions 8.1–8.2). On the minor arcs the prime-list graph exchanges primes in the active intervals. Fourier cancellation on unlinked steps and counting repeated prime constraints on linked steps enter the path moment (Propositions 9.1, 9.6 and 10.2). Proposition 7.1 gives arbitrary fixed log savings with the active pattern, one coefficient \(\mu(m)R_z(m)m^{iv}w(m)\) of controlled variation in \(w\), and a log-bounded second coefficient. The freedom in the second coefficient preserves the active-pattern requirement. [Determinant](/tmp/arxiv_nov2026/2611.28392v1/binary_chowla1.tex:988) · [Type II statement](/tmp/arxiv_nov2026/2611.28392v1/binary_chowla1.tex:1087) · [Graph and primitive endpoints](/tmp/arxiv_nov2026/2611.28392v1/binary_chowla1.tex:1362) · [Moment](/tmp/arxiv_nov2026/2611.28392v1/binary_chowla1.tex:1533)

[P] For \(v=qr\) with \(q,r\) prime there are at most two successful intervals, including when \(q=r\). Hence \(T(v)=0\), \(E(v)=1\) for **every** \(k\ge1\), without any limiting argument. If both factors exceed \(N^a\) with fixed \(a>0\), there are zero hits as soon as \(e^{(\log N)^\beta}<N^a\). On \(x\asymp N\) the same strict inequality holds eventually. Every active divisor sum is then empty. For an unbalanced semiprime a single small factor might be active, but no complete pattern survives. A prime complement also has \(T=0\). The partition is exact on the integers because it retains \(E\). The cancellation estimate acts on \(T\).

[P,Q] Equation (3.1) imposes \(\beta+\jmath<\varrho<1-\beta-\jmath\). In Lemma 9.5 the \(2R\)-th root must absorb the endpoint factor, with \(R\asymp L^\varrho\) and \(\log(DY)\ll L^{\beta+\jmath}\). In Proposition 10.2 the modulus and absolute path cost have logarithms \(\ll L^{\varrho+\beta+\jmath+o(1)}\), which must be \(o(L)\) in that proof. Thus \(\beta+\jmath<1/2\). Mertens gives an avoidance factor asymptotic to \(1/2\) per interval. The one-exception cost is \(2^{-B}B^{O_k(1)}=L^{-\gamma+o(1)}\). Two consecutive exceptions give \(L^{-2\gamma+o(1)}\) by Lemma 4.1. With \(\alpha=\epsilon/8,\ \beta=1/2-\epsilon/8\), a single exception costs \(L^{-1/2+\epsilon/4+o(1)}\). This is the source of the different exponents after absorbing log-log losses. [Parameter constraints](/tmp/arxiv_nov2026/2611.28392v1/binary_chowla1.tex:590) · [Exceptional sieve](/tmp/arxiv_nov2026/2611.28392v1/binary_chowla1.tex:675) · [Endpoint and path budgets](/tmp/arxiv_nov2026/2611.28392v1/binary_chowla1.tex:1522) · [Modulus budget](/tmp/arxiv_nov2026/2611.28392v1/binary_chowla1.tex:1645)

[P] One can see the cost on actual shifted primes. For primes \(p\in(x,2x]\) restrict to the zero-hit event for \(p+2\). At every ambient prime \(\ell\) the forbidden class is the unit \(-2\), of density \(1/(\ell-1)\). The dimension-one fundamental lemma with level \(x^{1/3}\), top sieve prime \(\le e^{L^\beta}\), and Bombieri–Vinogradov for the progression errors gives, relative to the primes in the interval, \((1+o(1))\prod_{\ell}(1-1/(\ell-1))=(1+o(1))2^{-B}\). Indeed the product over the contiguous union telescopes by Mertens to \(L^\alpha/(2^B L^\alpha)\), with the replacement of \(1/\ell\) costing \(1+o(1)\). The same sieve upper bound after permitting at most \(3k-1\) hit intervals costs \(O_k(B^{3k-1}2^{-B})\). For \(N-p\) at scale \(x\asymp N\) the forbidden class is \(N\bmod\ell\). Primes dividing \(N\) remove factors whose total reciprocal mass is \(O(\log N\,e^{-L^\alpha})\), and the prime inputs dividing \(N\) are negligible. BV with its residue maximum is uniform here. Thus even an exact count of exceptions at this resolution leaves this mass. A signed estimate *inside* the exceptions is a different input.

[P,I] Reflection changes the determinant too. Equal cofactors \((N-mn)/a=(N-rs)/b\) require \(bmn-ars=N(b-a)\). For distinct \(a,b\asymp Y=N^{o(1)}\), its magnitude exceeds the \(O(Y)\) cutoff of the published kernel. Remark 11.1 handles \(mn-1\) with determinant \(b-a\). Neither that reversal, ordinary prime EH, nor a Dirichlet ERH estimate supplies the new determinant analysis or puts semiprimes into \(T\). Even a stronger **global** signed bound allows cancellation between a band and its complement. [Fourier cutoff](/tmp/arxiv_nov2026/2611.28392v1/binary_chowla1.tex:1045) · [Reversed orientation](/tmp/arxiv_nov2026/2611.28392v1/binary_chowla1.tex:1860)

## 2. The normalization and the cost of a missing Goldbach pair

[P] Put \(b=1/2,\ a=b-\delta\), with \(1/3\le a<b\), and now \(L=\log N\). Write \(\mathfrak S=2C_2\prod_{\ell\mid N,\,\ell>2}(\ell-1)/(\ell-2)\) for the binary singular series, where \(C_2=\prod_{\ell>2}(1-1/(\ell-1)^2)\). Set \(X=\mathfrak S N/L\). For the literal ordered sum in the brief take
\[
 H=\mathrm{HL}_\delta(N)=\mathfrak S N\delta L.
\]
Indeed the continuum area is \(\int_{N^a}^{N^b}(N/q)\,dq=N\delta L\). For each prime \(\ell\), the number of pairs of units \((q,r)\) with \(N-qr\) a unit is \((\ell-1)^2\) if \(\ell\mid N\), and \((\ell-1)(\ell-2)\) otherwise. Dividing their density by \((1-1/\ell)^3\) gives exactly the displayed singular series. This defines a reference main term, without assuming a Hardy–Littlewood asymptotic for \(S_\delta\).

[P] All three von Mangoldt functions may include powers. Proper powers in \(p\) cost \(N^{1/2+o(1)}\) including the divisor multiplicity of \(N-p>0\). Proper powers in \(r\) cost \(N^{3/4+o(1)}\) by summing \(O(\sqrt{N/q}\,L)\) over \(q\le\sqrt N\). Proper powers in \(q>N^a\) cost \(N^{1-a/2+o(1)}\) by partial summation of their counting bound. These estimates absorb log weights. Prime rows \(q\mid N\) force \(p=q\) for prime inputs, with at most one \(r\) per row. Repeated factors \(r=q\) contribute \(O(\sqrt N L^3)\).

[P, conditional on ordinary prime EH] Let \(G_N=\sum_{p+\ell=N,\ p,\ell\ {\rm prime}}\log p\), counting ordered Goldbach pairs. The literal sum satisfies
\[
 \liminf_{2\mid N,\,N\to\infty}
 \left(\frac{S_\delta(N)}{\mathfrak S NL}+\frac{G_N}{4X}\right)\ \ge\ 2\delta. \tag{1}
\]
Consequently a fixed bound \(S_\delta\le(2-\eta+o(1))H\) implies \(G_N\ge(4\eta\delta-o(1))X\). Positivity is eventual. An effective finite bridge would still be needed for a statement covering every even \(N\ge4\).

[P] To prove (1), for fixed \(s\in[a,b)\) let \(F_N(s)\) count with weight \(\log p\) the prime triples with **smaller** factor \(N^s<q\le r\) and \(qr\ge N/L^4\). The prime-row lower linear sieve on \(N-p\), equation (2) of Wave 4, gives
\[
 \liminf (F_N(s)+G_N)/X\ \ge\ 2J(s),\qquad J(s)=\log((1-s)/s).
\]
In detail take a fixed \(2s<\theta<1\), use its lower coefficient \((2/\theta)\log((\theta-s)/s)\), and then let \(\theta\uparrow1\). Strict roughness and \(s\ge1/3\) permit at most two prime factors. Deleting \(1<qr<N/L^4\) costs \(O((N/L^4)L)=o(X)\) by counting integers once. The complement 1 and the exclusions \(p\mid N\) also cost \(o(X)\). This uses EH only for the prime being sieved. [Wave 4, lower sieve and normalization](B005_B012_W4_DECISIVE_PARITY_PHASE_DIAGRAM.md)

[P] Write \(t=\log q/L\), \(w(t)=t(1-t)\). On the retained range, \((\log q)(\log r)\ge L^2 w(t)(1-O(\log L/L))\) uniformly. The literal sum includes every retained triple with nonnegative weights even when its ordering admits additional triples. Layer integration gives \(w(a)F_N(a)+\int_a^b w'(s)F_N(s)\,ds\) for the retained measure weighted by \(w(t)\). Here \(w'\ge0\) and \(w(b)=1/4\). Add \(G_N\) to every tail, divide by \(X\), and use Fatou on these nonnegative quantities. Integration by parts with \(-J'(s)=1/w(s)\) and \(J(b)=0\) gives \(2[w(a)J(a)+\int_a^b w'J]=2\delta\). This proves (1), including for sequences of varying even targets. It avoids assuming that a bound with weight \(\log q\log r\) can simply be divided by a constant.

## 3. An exact deficit for a nonnegative dispersion majorant

[P, conditional on ordinary prime EH at level \(\theta\)] Fix \(b<\theta<1\). Take each prime row \(N^a<q\le N^b,\ q\nmid N\), set \(Z=(N^\theta/q)^{1/2}\), and majorize primality of \(r=(N-p)/q>Z\) by a real Selberg square \((\sum_{d\mid r,\ d\le Z}\lambda_d)^2\), with \(\lambda_1=1\) and squarefree \(d\) coprime to \(N\). The small primes \(r\le Z\) across all rows cost \(O(N^{(\theta+b)/2}L^3)\) by summing \(Z\). Majorize their larger counterparts’ weight by \(\log(N/q)\). The optimal resulting EH main-term coefficient relative to \(H\) is
\[
 C(\theta,a,b)=\frac{2}{b-a}\int_a^b\frac{1-t}{\theta-t}\,dt
 =2+\frac{2(1-\theta)}{b-a}\log\frac{\theta-a}{\theta-b}. \tag{2}
\]
In particular \(\limsup S_\delta/H\le 2\) under the full prime EH family. Together with (1) this forces \(S_\delta/H\to2\) on any hypothetical unbounded sequence of even Goldbach exceptions under EH. Formula (2) concerns this specified square, divisor cutoff and evaluation by progression main terms. The genuine signed prime dispersion problem remains open.

[P] **Finite diagonalization.** The row mass for the \(\log p\) measure is modeled by \(N/\varphi(q)\). The fraction with \(d\mid r\) is \(g(d)=\varphi(q)/\varphi(qd)\) for squarefree \((d,N)=1\). Thus \(g(\ell)=1/(\ell-1)\) for \(\ell\nmid Nq\), \(g(q)=1/q\), and we set \(g(\ell)=0\) on excluded primes. This includes the repeated modulus \(q^2\) when \(q\mid d\). On allowed squarefree integers put \(h(\ell)=g(\ell)/(1-g(\ell))\) multiplicatively, \(G(Z)=\sum_{j\le Z}h(j)\) with all sums below over this support, including 1. With \(y_j=\sum_{j\mid d}g(d)\lambda_d\) the entire main quadratic form becomes
\[
 Q=\sum_{d,e\le Z}\lambda_d\lambda_e g([d,e])
   =\sum_{j\le Z}y_j^2/h(j),\qquad \sum_j\mu(j)y_j=1 .
\]
The first identity expands \(1/g((d,e))=\sum_{j\mid(d,e)}1/h(j)\). Cauchy–Schwarz has exact minimum \(1/G(Z)\), attained at \(y_j=\mu(j)h(j)/G(Z)\). Inverting gives
\[
 \lambda_d=\frac{\mu(d)}{G(Z)}\prod_{\ell\mid d}(1-g(\ell))^{-1}
   \sum_{j\le Z/d,\,(j,d)=1}h(j).
\]
In particular \(|\lambda_d|\le1\) since each such \(j\) times every divisor of \(d\) occurs in \(G(Z)\). For these weights the **raw diagonal** is \(D_*=\sum_d g(d)\lambda_d^2\) and the **signed off-diagonal**, counting both orders, is exactly \(1/G(Z)-D_*\). Replacing the latter by an absolute value loses its leading cancellation.

[P] **Size of each part.** Uniformly in the rows, set
\[
 C_q=\prod_\ell\frac{1-g(\ell)}{1-1/\ell}
     =\mathfrak S\frac{(q-1)^2}{q(q-2)},\qquad
 K_q=\prod_\ell(1-1/\ell)(1+g(\ell))
     =\frac{\varphi(N)}{N}(1-q^{-2}).
\]
Then, with absolute exponents in the error terms for fixed \(a,b,\theta\),
\[
 G(Z)=\frac{\log Z}{C_q}+O((\log\log N)^{O(1)}),\qquad
 D_* = \tfrac13 K_q\log Z+O((\log\log N)^{O(1)}).
\]
The off-diagonal has leading term \(-K_q\log Z/3\); their **exact sum** is \(1/G(Z)=(1+o(1))C_q/\log Z\). Thus the large diagonal and off-diagonal of the sieve square already cancel to reciprocal-log size.

[P] For details, extend \(u=h\) or \(g\) by zero outside the squarefree support, also optionally excluding the primes dividing any \(d\le Z\). Convolve out \(n\mapsto1/n\). The residual Euler factors have coefficients \(1,u(\ell)-1/\ell,-u(\ell)/\ell\) at \(1,\ell,\ell^2\). Their nonconstant coefficients are \(O(1/\ell^2)\) off the excluded primes and \(q\). The absolute sum and its first logarithmic moment are \(O((\log\log N)^{O(1)})\): on primes dividing \(Nqd\) split at \((\log N)^2\), using Mertens below and \(\log(Nqd)=O(\log N)\) above. Summing the harmonic convolution through \(Y\ge1\) therefore yields its Euler product at zero times \(\log Y\) with that same absolute error (the omitted tail times \(\log Y\) is bounded by the logarithmic moment). For \(h\) that constant is \(1/C_q\); excluding \(\ell\mid d\) multiplies it by \(\prod_{\ell\mid d}(1-g(\ell))\). For \(g\) the constant is \(K_q\). All local products and their reciprocals here grow at most as a power of \(\log\log N\). Inserting these estimates into the minimizer gives \(\lambda_d=\mu(d)\log(Z/d)/\log Z+O((\log\log N)^{O(1)}/L)\) uniformly. Partial summation of \(g(d)(1-\log d/\log Z)^2\) gives the stated diagonal, since \(\int_0^1(1-u)^2du=1/3\).

[P] **Summing the rows.** Each remainder in the expanded square is a prime progression error at residue \(N\) modulo \(m=q[d,e]\le N^\theta\), coprime to the residue. For each \(m\) the number of triples is bounded by a fixed power of \(\tau(m)\). The two external logarithms cost \(O(L^2)\). Ordinary prime EH for \(\sum\log p\) in reduced classes with arbitrary log saving also controls this divisor-weighted absolute error. Indeed split by Cauchy–Schwarz, using EH for one factor and the trivial \(O((N/m+1)L+N/\varphi(m))\) bound with a fixed divisor moment for the other. Thus evaluation at the minimizing weights costs \(o(H)\) uniformly. Using \(N-p\ge1\) changes at most an endpoint. The optimized row, after multiplying by \(\log q\log(N/q)\), contributes main term
\[
 (1+o(1))\,\mathfrak S N\frac{\log q}{q}
              \frac{2(1-t)}{\theta-t},\qquad t=\log q/L .
\]
The relative error is uniform because \(\log Z\gg L\) and \(q>N^a\). The prime number theorem and partial summation give (2). Omitting \(q\mid N\) costs \(o(H)\) even with the local factors since \(q>N^a\). No progression theorem for a convolution of two primes was assumed. [P] For example \(a=0.45,\ b=0.5,\ \theta=0.99\) gives \(C=2.0388654993814591\ldots\).

[P] In particular, define the extended majorant by summing the square over **all** prime inputs \(p<N,\ p\equiv N\pmod q\) in each allowed row, with external factor \(\log q\log(N/q)\). Add the negligible small-prime and prime-power allowances above to cover the literal statistic. EH evaluates the extended majorant itself to \((C(\theta,a,b)+o(1))H\) at the minimizing weights. Every uniformly bounded family of row weights with the same support and \(\lambda_1=1\) has at least this asymptotic lower coefficient by the same uniform remainder bound. Hence any upper bound for this whole majorant, even one obtained by dispersion with exact off-diagonal evaluation, has coefficient at least \(C(\theta,a,b)\). To improve the literal statistic one could instead estimate the excess mass assigned to composite cofactors or retain genuine prime correlations before this majorization.

## 4. Direct Cauchy–Schwarz and Kloosterman fractions

[P] Take the literal sum, with von Mangoldt weights at positive integers and zero otherwise. Set \(u_q=\Lambda(q)/q\) on the band, \(A=\sum_q u_q\sim\delta L\), \(x_{qr}=q\Lambda(r)\Lambda(N-qr)\). Cauchy–Schwarz with this row weighting gives
\[
 S_\delta^2\le A(D+O),\quad
 D=\sum_q u_q\sum_r x_{qr}^2,\quad
 O=\sum_q u_q\sum_{r\ne s}x_{qr}x_{qs}. \tag{3}
\]
Here \(O\) denotes the **ordered off-diagonal**, which is nonnegative. The weighting compensates for the different row lengths \(N/q\). Trivially \(D\ll NL^4\sum_{q\le\sqrt N}\Lambda(q)\ll N^{3/2}L^4\), so \(AD/H^2=o(1)\) uniformly. The exact off-diagonal threshold for this inequality to certify \(S_\delta\le cH\) is \(AO/H^2\le c^2-AD/H^2\). Thus the limiting diagonal constant is **0** and the off-diagonal budget at \(c=2\) is **4**. The actual off-diagonal coefficient remains unknown. Under EH, (1) and (3) force \(\liminf AO/H^2\ge4\) along any unbounded sequence of Goldbach exceptions. **[U]** A uniform \(\limsup AO/H^2<4\) would suffice. A large row variance could make (3) loose even if the first moment is small.

[P] For \(r\ne s\) the inner dependence is the product \(\Lambda(q)\Lambda(N-qr)\Lambda(N-qs)\), with both reflected factors sharing \(q\). The determinant of the two affine forms has absolute value \(N|r-s|\). Ordinary EH compares a single prime weight in progression to its mean. It gives no stated estimate for this product. Transposing rows and columns gives two forms sharing \(r\) instead. On a rectangular subbox with probability weights on each variable, two applications of Cauchy–Schwarz bound the fourth power of the average of \(f(q,r)=\Lambda(N-qr)\) by the average of \(f(q,r)f(q,s)f(t,r)f(t,s)\) over independent copies of both variables. This follows by first squaring the row average, then squaring the paired column average. Nonrectangular support can be put inside \(f\). The second square still requires a prime correlation.

[P] For example, expanding divisor tests on both reflected forms and completing a **smooth** row gives congruences \(q\equiv N\bar r\pmod d,\ q\equiv N\bar s\pmod e\) on the unit ranges. They require congruence of these two residues modulo \((d,e)\). For coprime \(d,e\), Poisson summation gives at frequency \(h\) the phase
\[
 e\!\left(\frac{hN\bar r\bar e}{d}\right)
 e\!\left(\frac{hN\bar s\bar d}{e}\right)
\]
(up to the sign convention on the Fourier transform) and density \(1/(de)\) at frequency zero. In the unexpanded (3) the row has the prime weight \(\Lambda(q)\); smooth completion already requires a decomposition or a majorant. In the one-square computation of §3 even perfect control of the non-main progression terms leaves (2). In (3) no identity above reduces its prime correlation to a single separable inverse phase with negligible residual.

[Q,P] In Pascadi’s notation below let \(M\) be the common length bound for Theorems 1.1–1.2. The exact scope of the five results matters.

- [Q,P] **Theorem 1.1.** \(\sum_{(m,n)=1}\alpha_m\beta_n e(v\bar m/n)\ll\|\alpha\|_2\|\beta\|_2 M^{11/12+o(1)}\), \(m,n\le M,\ 0<|v|\ll M^{4/3}\). The target \(N\asymp M^2\) already exceeds this numerator range at balanced lengths for \(v=N\); reducing a residue separately for each modulus does not give a fixed numerator.
- [Q,P] **Theorem 1.2.** Summing \(1\le v\le V\ll M^{1/14}\) with its own coefficient replaces the bound by \(\|\alpha\|_2\|\beta\|_2\|\nu\|_2 M^{11/12+o(1)}V^{1/6}\). There is no free fixed multiplier \(N\) in this theorem. The paper also gives multiplier-dependent variants. A product of shared reflected prime weights still needs an arithmetic reduction before using them.
- [Q,P] **Theorem 5.1.** A smoothed shifted second moment of zeta at height \(T\) with a Dirichlet polynomial of length \(Y\le T^{207/389}\), shifts \(\ll1/\log T\), and error \(T^{o(1)}(T^{1/2}Y^{1/2}+T^{1/3}Y^{5/4}+T^{79/286}Y^{389/286})\). Its diagonal and zero frequency are for that height integral. A pointwise Goldbach row does not furnish this average.
- [Q,P] **Theorem 5.2.** For \(x\asymp M_1M_2\), divisor-bounded factors, the second Siegel–Walfisz, \(M_2\ge\exp((\log x)^\epsilon)\), and \(0<|v|\le x/12\), the mean AP discrepancy on unit moduli \(d\sim Q\) has arbitrary log saving if \(Q\le x^{-\epsilon}\min\{(x^{207}/M_2^{468})^{1/389},(x^{151}/(|v|^8M_2^{292}))^{1/277},x^{3/4}/(|v|^{1/4}M_2)\}\). Even giving it a small residue, the first exponent is negative when \(M_2=x^t\) with \(t>23/52\); it equals \(-27/389\) at balance. For \(x<qr\le2x\le 2N\) with \(x<N\), the natural residue \(v=N\) also violates \(|v|\le x/12\). This fails on a positive-width central subband.
- [Q,P] **Theorem 5.3.** For \(m_1n_2-m_2n_1=\Delta\ne0\), \(n_i\sim M\), two smooth weights \(f(m_1/M),g(m_2/M)\) and two arbitrary \(n_i\)-coefficients, the main term has \((n_1,n_2)\mid\Delta\), density \((n_1,n_2)/(n_1n_2)\) and the specified smooth overlap integral. Error divided by \(\|\alpha\|_2\|\beta\|_2 M^{o(1)}\) is \(\ll_{f,g}\min\{M^{19/20}, M^{11/12}+M^{7/8}|\Delta|^{1/32}+|\Delta|^{1/2}\}\). The \(M^{19/20}\) branch remains available for large shifts. The unsmoothed prime weights in the additional coordinates, and \(\Delta=0\) when indices coincide, require separate treatment.

[Q] Source locations for the five theorems. [Theorems 1.1–1.2](/tmp/arxiv_nov2026/2611.34917v1/main.tex:52) · [Theorem 5.1](/tmp/arxiv_nov2026/2611.34917v1/main.tex:3044) · [Theorem 5.2](/tmp/arxiv_nov2026/2611.34917v1/main.tex:3148) · [Theorem 5.3 and its Poisson formula](/tmp/arxiv_nov2026/2611.34917v1/main.tex:3234)

[P] Finite checks used exact rational arithmetic for the optimal Selberg weights and 128-bit Arb for the prime moment. At \(N=30030,q=17,Z=40\) the raw diagonal and off-diagonal have common denominator \(89483672695561\) and numerators \(105155360346722\) and \(-34642130039762\). Their sum is exactly \(1/G=7454160/9459581\). A separate enumeration at \(N=2000,19<q\le44\) checks (3) with all von Mangoldt powers. The checks concern these finite instances. [Replay script](/tmp/astra_w5_1a/check.py) · [Interpreter](/tmp/astra_w2_b011/venv/bin/python)

**[U] Verdict.** The missing input can be stated as a fixed saving in the one-sided first moment or, more strongly, a uniform off-diagonal saving below 4 in (3). The infimum 2 in (2) rules out obtaining that first-moment saving solely by optimizing this progression-evaluated Selberg square. A general impossibility result for dispersion, or a strict saving for genuine primes, remains unproved.

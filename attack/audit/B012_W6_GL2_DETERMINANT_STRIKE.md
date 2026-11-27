# B-012 · The prime determinant and its second moment

**[U] No-go for the proposed direct spectral application.** None of the three regimes examined here supplies a uniform coefficient below 4. **[P]** The determinant in the brief comes from transposing the Wave 5 sum. Its right side depends on the two moduli in precisely the way that cancels the modular inverse in the direct Poisson formula. **[P, conditional on ordinary prime EH]** For the *original* Wave 5 moment, the normalized off-diagonal lies between the square of the normalized first moment and twice that first moment, up to \(o(1)\). Thus, even a strict saving of 0.01 below 4 would require a strict first-moment saving. Conversely a first-moment saving suffices for a second-moment saving. This comparison is uniform in the even target. **[I]** It identifies a precise obstruction for the optimized product of sieve squares. It leaves open other decompositions of the genuine prime weights.

[Q] denotes a source statement, [P] a derivation or finite calculation here, [I] an interpretation or heuristic prediction, and [U] an unproved input. All analytic arguments here are on paper. The numerical check is finite. There is no Lean verdict.

## 1. Three different choices of the common variable

[P] Fix \(a=1/2-\delta,\ b=1/2,\ 1/3\le a<b\), independently of \(N\). Put \(I=(N^a,N^b]\cap\mathbb Z,\ L=\log N,\ V=N\delta L,\ H=\mathfrak S(N)V\), where
\[
 s_\ell=\frac{\ell k_\ell}{(\ell-1)^2},\qquad
 k_\ell=\ell-1-\mathbf1_{\ell\nmid N},\qquad \mathfrak S(N)=\prod_\ell s_\ell .
\]
For even \(N\), \(\mathfrak S\gg1\) and \(\mathfrak S\ll\log\log(3N)\) by the Euler product and Mertens' bound (split divisors of \(N\) at \((\log N)^2\)). Take all positive arguments with \(q\in I,\ p=N-qr\ge1\), and include prime powers in \(\Lambda\). Write \(S=\sum\Lambda(q)\Lambda(r)\Lambda(p)\). The denominator \(H\) is a reference value. [Wave 5, §§2–4](B012_W5_LICHTMAN_SEMIPRIME_STRIKE.md)

**[P] Common \(q\), exactly as in Wave 5.** Set \(A=\sum_{q\in I}\Lambda(q)/q\sim\delta L\) by the prime number theorem, \(Y_q=\sum_r\Lambda(r)\Lambda(N-qr)\). Then
\[
 D_q+O_q=\sum_{q\in I}q\Lambda(q)Y_q^2,\qquad
 O_q=\sum_q q\Lambda(q)\sum_{r\ne s}
 \Lambda(r)\Lambda(s)\Lambda(N-qr)\Lambda(N-qs).
\]
Subscripts label the grouping. Off-diagonals count both orders. \(S^2\le A(D_q+O_q)\), and \(D_q\ll N^{3/2}L^4\), since there are at most \(N/q\) cells in a row. In particular \(AD_q/H^2=o(1)\). The two reflected primes obey \(p_1-p_2=q(s-r)\). Eliminating the common \(q\) also gives \(s p_1-r p_2=N(s-r)\) with cofactors \(r,s\) of their own lengths.

**[P] Common \(r\), giving the requested determinant.** Put \(I_r=\{q\in I:qr<N\}\), \(J_r=|I_r|\), \(Z_r=\sum_{q\in I_r}\Lambda(q)\Lambda(N-qr)\). Use the outer mass \(B=\sum_r\Lambda(r)J_r\), omitting empty rows. Then
\[
 D_r+O_r=\sum_{J_r>0}\frac{\Lambda(r)}{J_r}Z_r^2,\qquad
 O_r=\sum_{J_r>0}\frac{\Lambda(r)}{J_r}\sum_{q_1\ne q_2\in I_r}
 \Lambda(q_1)\Lambda(q_2)\Lambda(N-q_1r)\Lambda(N-q_2r).
\]
Here \(S^2\le B(D_r+O_r)\). Interchanging the sums and applying the prime number theorem uniformly at lengths \((N-1)/q\gg\sqrt N\) gives \(B\sim V\). Since \(D_r\le L^4\sum_{r<N^{1-a}}\Lambda(r)\ll L^4 N^{1-a}\), \(BD_r/H^2=o(1)\), even for single-cell rows. The threshold for this grouping is also 4, with **its own** numerator and prefactor. Each tuple has five Mangoldt weights, including the common cofactor.

**[P] Common \(p\).** With \(P=\sum_{p<N}\Lambda(p)\sim N\), put \(W_p=\sum_{q\in I,\ q\mid N-p}\Lambda(q)\Lambda((N-p)/q)\). Now \(S^2\le P\sum_p\Lambda(p)W_p^2=P(D_p+O_p)\). For genuine primes, unique factorization implies that the only off-diagonal is reversal \((q,r)\leftrightarrow(r,q)\) with both factors in \(I\) and \(q\ne r\). The diagonal includes every triple with squared factor weights. Proper powers can be removed from these moment comparisons with a power saving times \(N^{o(1)}\) in the first-moment scale: Wave 5 §2 bounds the total weight of triples involving a proper power by \(N^{1-\kappa+o(1)}\) for some fixed \(\kappa>0\). In common-\(p\) rows the second factor costs at most \(\tau(N-p)L^2=N^{o(1)}\). In common-\(q,r\) rows the companion cell sum divided by row length is \(O(L^2)\), including rows supported on prime powers. The same bounds hold after interchanging the two copies. [Wave 5, prime powers](B012_W5_LICHTMAN_SEMIPRIME_STRIKE.md)

[P] For example, if \(S\gg H\), restrict to \(qr\ge N/L^{10}\). Removing smaller products costs at most \(L^3\sum_{q\in I}N/(qL^{10})\ll N/L^6\). On retained genuine triples, \(\log q\log r\gg_a L^2\). Thus \(PD_p/H^2\gg_\delta L/\mathfrak S\to\infty\). The negligible-diagonal inference fails for this grouping, even under a first moment of the conjectured size.

## 2. Hardy–Littlewood prediction and the lattice of the determinant

[P] The local moment computation can be made before invoking any heuristic. Modulo \(\ell\), require the common variable \(x\), two inputs \(y,z\), and both reflections \(N-xy,N-xz\) to be units. There are exactly \((\ell-1) k_\ell^2\) possibilities out of \(\ell^3\). Dividing by \((1-1/\ell)^5\) gives **exactly \(s_\ell^2\)**, including \(\ell=2\) and every prime divisor of \(N\). Distinct inputs can coincide modulo a small prime. Excluding that residue diagonal would give a wrong factor. The global equal-input diagonal has already been bounded separately.

[I] In the Hardy–Littlewood model the archimedean mass of the common-\(q\) square is \(\int_{N^a}^{N^b}q(N/q)^2\,dq=N^2\delta L\). For common \(r\), weighting the square by inverse row length leaves one row length, whose integral is \(V\). Consequently the predicted normalized off-diagonal is **1 in both groupings**, against a threshold of **4**. This predicts a factor of four in the second moment, or two in the first. It gives no uniform error bound. The prediction for the common-\(p\) square differs: on reversal, the two additional logarithms give an integral \(\mathfrak S(\int_{N^a}^{\sqrt N}\log u\,du)^2\sim\mathfrak S N L^2/4\). This predicts \(PO_p/H^2\sim1/(4\mathfrak S\delta^2)\). The predicted normalized diagonal is \(L\int_a^b t(1-t)\,dt/(\mathfrak S\delta^2)\), by inserting the extra \(\log q\log r\) into the first-moment integral.

[P] For distinct prime \(q_1,q_2\) the determinant
\[
 q_2p_1-q_1p_2=h,\qquad h=N(q_2-q_1)
\]
implies \(p_i\equiv N\bmod q_i\). Conversely every solution with \(0<p_i<N\) has a unique positive integer \(r=(N-p_i)/q_i\), the same for both coordinates. The homogeneous lattice direction is \((q_1,q_2)\); the affine parametrization is \((N,N)-r(q_1,q_2)\). There are exactly \(\lfloor(N-1)/\max(q_1,q_2)\rfloor\) unweighted positive solutions with \(p_i<N\). The determinant alone permits every integer \(r\) in that interval. It does not impose its prime weight \(\Lambda(r)/J_r\).

[P] On a comparable dyadic block \(q_i\asymp Q=N^t,\ a\le t\le1/2\), set \(d=|q_2-q_1|\). The lattice length is \(\asymp N/Q\), \(q_1q_2\asymp N^{2t}\), and \(|h|=Nd\) ranges up to \(O(N^{1+t})\). For \(d\asymp Q\) at the logarithmic midpoint this is \(N^{3/2-\delta/2}\); at the lower edge it is \(N^{3/2-\delta}\). A narrow difference gives a smaller shift. For unequal boxes use \(\max(q_i)\) in the length and retain the actual product \(q_1q_2\). There is no single conductor or height intrinsic to the affine equation.

[P] Direct Poisson summation for smooth \(p_2\) in its residue class produces \(e(-k h\overline{q_1}/q_2)=e(kN/q_2)\), because \(h\overline{q_1}\equiv-N\bmod q_2\). Here \(e(x)=\exp(2\pi i x)\). Equivalently the class is simply \(p_2=N\bmod q_2\). Thus this Poisson phase has **no inverse dependence on \(q_1\)** for the prime pair average to exploit. On replacing all arithmetic weights by a smooth function of \(r/R,\ R\asymp N/Q\), the lattice count has a zero mode of order \(R\); its other modes are \(O_A(R^{1-A})\) for a fixed smooth compactly supported profile, by integration by parts. Restoring \(\Lambda(r)\Lambda(N-q_1r)\Lambda(N-q_2r)\) is exactly the arithmetic difficulty.

## 3. Which Selberg product actually has constant 4?

[P] Use \(d\mu(q)=\Lambda(q)/(qA)\) on \(I\), \(T_q=qY_q/(N\mathfrak S)\), \(s_N=S/H\), \(o_N=AO_q/H^2\). Exactly,
\[
 s_N=\frac A{\delta L}\mathbb E_\mu T_q,\qquad
 o_N=\left(\frac A{\delta L}\right)^2\mathbb E_\mu T_q^2-\frac{AD_q}{H^2}.
 \tag{1}
\]

**[P, ordinary prime EH] Product of the optimized cofactor squares.** For each fixed \(b<\theta<1\), in a prime row \(q\nmid N\) let \(R=(N-1)/q,\ Z=(N^\theta/q)^{1/2}\). Write \(M_q\) for the Wave 5 extended square for primality of **\(r\)**, in \(T_q\) units:
\[
 M_q=\frac{q\log(N/q)}{N\mathfrak S}
 \sum_{\substack{p<N,\ p\ {\rm prime}\\p\equiv N\bmod q}}\log p
 \left(\sum_{\substack{d\mid(N-p)/q\\d\le Z}}\lambda_{d,q}\right)^2.
\]
Use the minimizing weights of Wave 5 §3, with \(|\lambda_{d,q}|\le1\). Define \(M_q=0\) on the exceptional rows. Then, for \(t=\log q/L\),
\[
 \left\|M_q-c_\theta(t)\right\|_{L^2(\mu)}=o(1),\qquad
 \left\|(T_q-M_q)_+\right\|_{L^2(\mu)}=o(1),\qquad
 c_\theta(t)=\frac{2(1-t)}{\theta-t}.
 \tag{2}
\]

[P, proof under EH] The finite quadratic form gives the progression main term \(c_\theta(t)+o(1)\) uniformly in admissible rows, using the \(G(Z)\) asymptotic and the \(q/\varphi(q)\) factor in Wave 5. For the *arithmetic remainder alone*, the \(\mu\)-mean absolute value is \(O_B(L^{-B})\) for each fixed \(B\): expand the square, multiply by \(d\mu\), and group the errors by \(m=q[d,e]\le N^\theta\). After the \(q\) in \(M_q\) cancels \(1/q\), only external logarithms, \(1/(AN\mathfrak S)\), and multiplicities \(\ll\tau(m)^{O(1)}\) remain. Divisor-weighted EH follows by Cauchy–Schwarz as in Wave 5 §3, with arbitrary log saving. To pass to \(L^2\), \(M_q\ll L^2 R^{-1}\sum_{r\le R}\tau(r)^2\ll L^5\), using \(\tau^2\le\tau_4\); the normalized progression main terms are bounded. Multiply the mean absolute arithmetic remainder by this polylogarithmic supremum. The deterministic uniform \(o(1)\) is handled separately. The \(\mu\)-mass of prime powers \(q\) of exponent at least 2 or primes \(q\mid N\) is \(N^{-a/2+o(1)}\). For genuine \(r>Z\) the square equals one at primes. Small \(r\le Z\) and proper powers have power-saving first-moment mass as in Wave 5. Their normalized row contributions are bounded by \(O(L^2)\), so their \(L^2(\mu)\) norms vanish too. These arguments establish both assertions of (2). [Wave 5, finite minimization and uniform progression errors](B012_W5_LICHTMAN_SEMIPRIME_STRIKE.md)

[P, ordinary prime EH] Squaring this particular extended majorant gives the following *actual* normalized limiting coefficient, for each fixed \(\theta\):
\[
 \frac1\delta\int_a^b c_\theta(t)^2\,dt
 =4\left[1+\frac{2(1-\theta)}{\delta}\log\frac{\theta-a}{\theta-b}
          +\frac{(1-\theta)^2}{(\theta-a)(\theta-b)}\right].
 \tag{3}
\]
This uses (2) and prime partial summation. Deleting its equal-cell terms costs \(o(1)\): each expanded squared-divisor weight per cell is \(N^{o(1)}\), and the normalized weighted cell diagonal has the same power saving as \(AD_q/H^2\). Hence the infimum of this extended product's coefficient is exactly **4**, approached as \(\theta\uparrow1\). This identifies which variables the rigorously evaluated \(2\times2\) calculation majorizes.

**[P, ordinary prime EH] One side and the genuine second moment.** First take \(N\to\infty\) for fixed \(\theta\), then \(\theta\uparrow1\). Equation (2) gives \(\|(T_q-2)_+\|_2=o(1)\), since \(c_\theta\to2\) uniformly. In particular \(\|T_q\|_2\le2+o(1)\). One may majorize just one side:
\[
 \mathbb E T_q^2\le 2\mathbb E T_q+
       \|T_q\|_2\|(T_q-2)_+\|_2.
\]
Combining with (1), nonnegative variance and the diagonal estimate yields
\[
                   s_N^2-o(1)\ \le\ o_N\ \le\ 2s_N+o(1). \tag{4}
\]
This gives a precise test for a one-sided saving. If \(s_N\le2-\eta+o(1)\), then \(o_N\le4-2\eta+o(1)\). If \(o_N\le4-\varepsilon+o(1)\), then \(s_N\le\sqrt{4-\varepsilon}+o(1)\). Under the same EH hypothesis Wave 5 proves \(s_N\to2\) along any unbounded sequence of exceptions. Thus along such a sequence \(o_N\to4\) and \(\mathbb E(T_q-2)^2\to0\). The quantified result concerns the common-\(q\) grouping. No interchange of \(\theta\) and an ineffective \(N_0(\theta)\) is needed.

**[P] Two squares on the reflected \(p_i\) are a different calculation.** In the common-\(q\) grouping the two remaining coordinates \(r,s\) range independently before deleting the diagonal, so the fully majorized moment is literally a product of row masses. Let \(Z_p=N^\alpha\) be the **divisor cutoff**, not the expanded progression level. The latter can be \(Z_p^2\). Use the prime input \(r\) of length \(R\asymp N^{1-t}\) as the progression sequence, and majorize \(\Lambda(N-qr)\) on primes above \(Z_p\) by \(L(\sum_{d\mid N-qr}\lambda_d)^2\). For \(q\) prime, \(q\nmid N\), the sieve density is \(g(\ell)=1/(\ell-1)\) off \(Nq\), zero on the excluded primes dividing \(Nq\). The normalizing product \(\prod(1-g(\ell))/(1-1/\ell)\) is \(\mathfrak S(q-1)/(q-2)\). This follows because \(r\equiv N\bar q\bmod d\) is one reduced class for each allowed \(d\). The same finite minimization and harmonic-sum proof as in Wave 5 therefore give a row main-term multiplier \((1+o(1))/\alpha\) in \(T_q\) units. Small reflected primes and proper powers have power-saving aggregate cost for fixed \(\alpha\le1/2\); for example \(p\le\sqrt N\) admits at most \(\tau(N-p)\) factorizations. The diagonal deletion still costs \(o(1)\) for bounded sieve coefficients.

[P] If those row main terms could be evaluated at \(\alpha_1=\alpha_2=1/2\) with negligible product error, the double reflected-prime cost would be 4. More generally the formal main term is \(1/(\alpha_1\alpha_2)\ge4\). With only one such factor the other row is still \(T_q\); its average against that majorant has to be estimated. Positivity alone gives neither 2 for the mixed product nor 3.99 for the double product. These are statements about the specified unweighted-in-the-divisors extension and its progression main terms. The goal is an upper bound for genuine prime mass, which can be smaller than the extension.

[P, ordinary prime EH] For **this rowwise reflected-prime evaluation**, the justified range is \(Z_p^2\le R^\theta,\ \theta<1\). At \(Z_p=R^{\theta/2}\) the normalized row main term is \(2/[\theta(1-t)]+o(1)\). Here EH at length \(R\) controls the absolute sum over \(d\le R^\theta\) with maximum over reduced residues, uniformly in \(q,N\); the divisor multiplicities are handled as above. The uniform remainder is smaller than any fixed inverse log after normalization, and the uniform minimization error is \(o(1)\). Thus the product coefficient for two such extended rows is
\[
 \frac1\delta\int_a^b\frac{4\,dt}{\theta^2(1-t)^2}
 =\frac{4}{\theta^2(1-a)(1-b)} .
\]
At \(\theta\uparrow1\) this approaches 16 as the band narrows to \(t=1/2\). At fixed \(\delta>0\) its value is \(4/[(1-a)(1-b)]>4\). If “level \(N^\alpha\)” means the *expanded modulus ceiling*, the divisor cutoff is \(N^{\alpha/2}\) and the formal single-square multiplier is \(2/\alpha\). Mixing the two definitions of level changes the answer.

[P, ordinary prime EH] More precisely, retaining one genuine side and using this justified reflected-prime square on the other gives normalized mixed mass
\[
 \mathbb E_\mu\!\left[\frac{2}{\theta(1-t)}T_q\right]+o(1).
\]
This follows from the uniform prime-row evaluation just given, (2) on genuine rows and the negligible diagonal. On a hypothetical unbounded sequence of exceptions, (4) and the first-moment limit give \(\|T_q-2\|_2\to0\), so the mixed mass tends to \(4\log((1-a)/(1-b))/(\theta\delta)>4\). The inequality follows by integrating \(1/(1-t)>1\) across the band. A one-side substitution on this available modulus range therefore also requires new information to certify a strict saving. [P, using Bombieri–Vinogradov] As a baseline independent of prime EH, the same reflected-prime calculation works with any fixed \(\theta<1/2\) at length \(R\). Taking its limit from below gives a uniform common-\(q\) off-diagonal upper coefficient \(16/[(1-a)(1-b)]\). This bound holds under each of the three spectral assumptions as well; it is far above 4.

[P] For the common-\(r\) determinant, expanding a square on each \(p_i\) fixes \(d_i=[u_i,v_i]\mid N-q_ir\). On unit ranges \(r\equiv N\bar q_i\bmod d_i\); the two classes must agree modulo \((d_1,d_2)\) and then give one class modulo \([d_1,d_2]\). Thus the fixed-pair local densities can correlate. Even with equal dyadic \(q_i\asymp Q\), the expanded modulus can reach \(Z_1^2 Z_2^2\) on coprime terms before any exploitation of cancellation. A direct termwise EH range on \(r\) would require \(2(\alpha_1+\alpha_2)\le\theta(1-t)\) to guarantee coverage by support alone. We have not assigned a product constant to this correlated progression calculation. A one-side pointwise majorant is permissible by positivity, but its mixed term still involves genuine prime correlation.

## 4. Decomposition and spectral range

**[P] A signed decomposition with its residual displayed.** The exact convolution identity \(\Lambda(p)=\sum_{uv=p}\mu(u)\log v\) follows from \(\log=1*\Lambda\) and Möbius inversion. Applying it twice and splitting into dyadic ranges gives the inner equation
\[
 q_2u_1v_1-q_1u_2v_2=h,\qquad
 r=(N-u_1v_1)/q_1>0 .
\]
Its coefficient contains \(\mu(u_1)\mu(u_2)\log v_1\log v_2\), and the common weight \(\Lambda(r)/J_r\). This is an exact alternative to a Vaughan or Heath–Brown splitting. On the balanced Type II pieces \(u_i,v_i\asymp\sqrt N\) (reflections of size \(\asymp N\)), the congruences \(u_i\mid N-q_ir\) have combined modulus \(m=[u_1,u_2]\asymp N\) for coprime \(u_i\) coprime to \(Nq_1q_2\). The length available for \(r\) is \(R\asymp N^{1-t}\). For fixed \(q_1,q_2,u_1,u_2\), the unweighted progression has mass \(R/m+O(1)\) in an interval of length \(R\), with \(R/m\asymp N^{-t}\). This is a range failure of termwise progression evaluation. It does not rule out cancellation after averaging the signed coefficients. Replacing \(\mu\) by absolute values yields divisor correlations with different main terms and loses the prime normalization. In particular an asymptotic for \(\tau_2\times\tau_2\) alone would not give (4) a strict margin.

[P] A separate way to see the coefficient problem is the exact circle integral for the equation, using \(1_{u=0}=\int_0^1e(\beta u)\,d\beta\). Take fixed coprime \(q_i\) and \(0<p_i<N\). In the \(p_1\)-sum insert \(\mathbf1_{q_1\mid N-p_1}\Lambda((N-p_1)/q_1)/J_{(N-p_1)/q_1}\) on admissible rows. The other factors in the integral are the additive twists of \(\Lambda(p_1),\Lambda(p_2)\) at \(\beta q_2,-\beta q_1\) and \(e(-\beta h)\). On a smooth dyadic box, replacing the two prime weights by level-one Hecke coefficients or the divisor function and omitting the extra row weight gives a recognizable GL₂ shifted-convolution problem. Reinstating either the prime coefficients or that row weight needs an identity or an error estimate. The signed convolution above exposes the terms such an estimate has to cover.

**[P] Modulus and dual lengths for the comparison problem.** At a reduced circle fraction \(j/c\), the two additive-twist denominators are \(c_i=c/(c,q_{3-i})\). For a fixed level-one form and a smooth, nonoscillatory test on \(p_i\asymp N\), GL₂ Voronoi has twist conductor \(c_i^2\) and effective dual length \(c_i^2/N\), up to \(N^\epsilon\), from its Bessel argument \(4\pi\sqrt{n p_i}/c_i\). The divisor formula additionally has a zero-frequency main term. On a balanced displacement scale \(X=NQ\), a delta-symbol choice \(C\asymp\sqrt X\) gives \(c\asymp C,\ (c,q_1q_2)=1\) and comparison dual lengths \(N^t\). On these top moduli with fixed smooth delta weights this scale has bounded rescaled derivatives. It is not a height bound for a transformed prime weight. In the model with both Voronoi formulas applicable, summing the numerator \(j\bmod c\) produces Kloosterman phases with arguments \(-h\) and \(\pm n_1\overline{q_2}\pm n_2\overline{q_1}\bmod c\). The latter residue varies with \(c\), so even this model requires specifying cusps or further reciprocity before inserting a fixed pair of indices in Kuznetsov.

[P] An alternative comparison lifts two level-one forms by \(z\mapsto q_i z\); their product then has \(q_1q_2\) as an admissible congruence level for distinct prime \(q_i\). This permits oldforms of smaller conductor. For a weight-zero primitive Maass constituent of arithmetic conductor \(F\mid q_1q_2\) and real Laplace parameter \(t_f\), the standard analytic conductor at \(1/2+i\tau\) is of order \(F(1+|\tau+t_f|)(1+|\tau-t_f|)\). The equation gives neither the spectral transform nor its range in \(t_f\). Rankin–Selberg conductors additionally depend on the actual local representations. Substitution of \(q_1q_2\) for every conductor and of \(\sqrt{|h|}\) for a spectral cutoff would not follow from these identities.

**[Q,P] What the cached spectral estimates actually say.** Deshouillers–Iwaniec's Kuznetsov framework relates smoothly weighted sums \(S(m\bar r,n;sc)\) over \(c\), on coprime cusp parameters \(r,s\), to level \(rs\) spectral coefficients. In Pascadi's level-averaged exceptional-spectrum theorem the test sequence is specifically \(\Psi(n/Y)e(t'n/F)\) at level \(F\) with a prescribed admissible range for \(X\) and an arithmetic occupancy bound on the level/phase weights. The spectral factor is \(X^{2\theta_f}\), \(\theta_f^2=1/4-\lambda_f\). Lowering \(\theta_f\) controls that factor. There is no corresponding insertion for \(\Lambda(r)\Lambda(N-q_1r)\Lambda(N-q_2r)\). A Blomer–Harcos shifted-convolution expansion for automorphic coefficients would require such coefficients and an admissible test on its input. An application of a Petersson, Deshouillers–Iwaniec, or Assing–Blomer–Li estimate would require an actual weighted Kloosterman family after the arithmetic reduction. No such transfer with a bounded prime residual is available in this calculation. [Kuznetsov setup](/tmp/arxiv_nov2026/2611.34917v1/main.tex:647) · [Level-dependent sequence and sieve](/tmp/arxiv_nov2026/2611.34917v1/main.tex:2286)

[Q,P] Pascadi's Theorem 5.3 has two arbitrary sequences and **two smooth weights on the same scale** \(M\), for a *fixed* determinant \(\Delta\). Its \(M^{19/20+o(1)}\|\alpha\|_2\|\beta\|_2\) branch has no small-shift restriction, while the balanced support itself forces \(|\Delta|\ll M^2\). Our \(p_i\asymp N,\ q_i\asymp Q\) are unbalanced and the shift moves with \(q_2-q_1\). Grouping by \(d=q_2-q_1\) would leave the extra relation between the two sequence indices, together with the three prime weights in \(r,p_1,p_2\). Smoothing only the \(p_i\) would also change the mass. Thus importing the exponent \(19/20\) would estimate a different sum. [Theorem 5.3 and Poisson expansion](/tmp/arxiv_nov2026/2611.34917v1/main.tex:3234)

[P,Q] There is an explicit exponent obstruction even for a *hypothetical* separated inverse-fraction sum with fixed multiplier \(v=N\), \(m,n\asymp Q=N^t\). Pascadi's multiplier-dependent bilinear estimate, relative to \(Q^{1+o(1)}\|\alpha\|_2\|\beta\|_2\), has the following bracket:
\[
 Q^{-1/12}+|v|^{1/32}Q^{-1/8}+|v|^{1/2}/Q
 =N^{-t/12}+N^{(1-4t)/32}+N^{1/2-t}.
 \tag{5}
\]
The last exponent is zero at balance and positive throughout the interior of the band. Intersecting this bound with trivial Cauchy–Schwarz yields no power saving there. In the underlying spectral amplifier bound the summand \(\sqrt{|v|A'}/Q\) is independent of the exceptional exponent, with \(A'=1\) for one numerator. The range \(0<|v|\ll Q^{4/3}\) of Theorem 1.1 also fails. Equation (5) is a limitation of the displayed estimates. It is not a lower bound on an exponential sum. In the *actual* direct determinant Poisson calculation even this hypothetical inverse fraction collapses to a single-modulus phase (§2). [Multiplier corollary](/tmp/arxiv_nov2026/2611.34917v1/main.tex:2919) · [Amplifier bound before optimization](/tmp/arxiv_nov2026/2611.34917v1/main.tex:2852)

| Assumptions on GL₂ | Spectral parameter contribution | Exponents on the comparable box and consequence |
|---|---|---|
| [Q,P] Unconditional | Exceptional \(\theta_f\le7/64\); \(X^{2\theta_f}\le X^{7/32}\) for \(X\ge1\). | Progression length/modulus \(N^{-t}\) on coprime balanced Type II terms. Formula (5) contains \(N^{1/2-t}\). No strict coefficient for the prime sum follows. |
| [P] Selberg and Ramanujan–Petersson | Selberg removes the exceptional spectrum. Finite-prime temperedness bounds Hecke coefficients of forms in an applicable expansion. | Same length/modulus \(N^{-t}\) and same \(\theta_f\)-independent multiplier term \(N^{1/2-t}\). No estimate of the signed prime residual follows. |
| [P,U] Grand RH for standard GL₂ and Rankin–Selberg \(L\)-functions | Critical-line zeros concern the specified \(L\)-functions. They neither identify a prime-weight expansion nor specify its spectral range. Even granting temperedness additionally leaves the preceding arithmetic terms. | Same exponent pair \((-t,1/2-t)\) for these calculations. No target-specific exponent for the genuine residual can be deduced by substituting an RH bound in them. |

[P] In particular \(h\ne0\) removes the identical \(q\)-cell from \(O_r\), but it leaves the whole \(r\)-progression above. Likewise the \(q\)-row square contains a square of its row mean even after removal of its negligible cell diagonal. A diagonal term in an auxiliary spectral large sieve would involve equality of its own coefficient indices and would need its own subtraction or evaluation. Equating these three notions of diagonal would discard main terms. Averaging over \(q_i\) is already in \(O_r\); it could help after a different arithmetic decomposition. Neither averaging over the target \(N\) nor treating \(h\) as independent of the \(q_i\) establishes the required uniformity.

## 5. Verdict and finite replay

**[P, ordinary prime EH]** The closed-form obstruction is (3) for the product of the two optimized **cofactor** majorants. Equation (4) further ties a strict improvement in the genuine common-\(q\) moment to a strict first-moment improvement. **[P]** The common-\(r\) determinant has a degenerate inverse phase, and the demonstrated Type II progression and separated-multiplier bounds have exponents \(-t\) and \(1/2-t\) respectively. **[U]** A uniform one-sided estimate for the genuine prime residual, with its arithmetic weights and its sign, is missing in all three regimes. No general impossibility theorem for GL₂ methods and no proof or refutation of binary Goldbach follows.

[P] A finite replay enumerated positive Mangoldt triples at \(N=4096,\ 16<q\le64\) with 128-bit Arb, including proper powers. Direct ordered-pair enumeration in the three groupings gave 1266, 334 and 52 pairs, respectively. Each grouping reproduced the same first moment and its own diagonal-plus-off-diagonal expansion. Integer tests checked the congruence phase on coprime pairs, prime-factor reversal, and all 41 target residues for primes through 13. Runtime was below 0.1 seconds locally. The replay verifies the finite identities and does not test EH or an asymptotic constant. [Replay script](/tmp/astra_w6_2b/check.py) · [Interpreter](/tmp/astra_w2_b011/venv/bin/python)

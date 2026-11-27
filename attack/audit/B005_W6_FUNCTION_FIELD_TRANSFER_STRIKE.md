# B-005 · Transferring the polynomial Goldbach cutoff to the integers

**[P] Go on the divisor identity. [U] No-go on an integer Goldbach proof from the cited inputs.** The integer short divisors already produce the full positive Hardy–Littlewood main term at a Bombieri–Vinogradov cutoff. The long divisors give a signed sum of Möbius values at \((N-p)/k\), with the strict endpoint \(p<N-kD\). Their support admits squarefree integers with many prime factors. The missing estimate is an **upper bound on the aggregate signed tail at each even \(N\)**. The function-field proof obtains an absolute power saving on affine families with determinant equal, up to sign, to the entire target. The integer results examined here do not supply that uniformity. Equations (5) and (9) below give, respectively, the minimal one-sided criterion and a stronger two-form input that would suffice.

[Q] identifies a source statement, [P] a derivation or executed finite check, [I] an interpretation and [U] an unresolved estimate. These are research notes. No theorem in this report has a Lean verdict.

## 1. What the function-field proof uses

[Q] GWX fix an **odd prime power** \(q>10^{200}\), including prime fields. For every monic \(N\) of degree \(d\ge3\), they state \(\sum_{F\in\mathcal M_{d-1}}\Lambda(F)\Lambda(N-F)=q^{d-1}\mathfrak S_q(N)+O_q(q^{23d/24})\), uniformly in \(N\), with \(q\) fixed as \(d\) grows. Here \(\Lambda(P^a)=\deg P\). The analogous difference theorem has scale \(q^n\) and error \(O_q(q^{23n/24})\). The authors identify \(q=p,p^2\) as the new cases for the leading asymptotic. [P] The series has a positive lower bound depending only on \(q\), by its Euler factors. Proper powers of degrees \(d,d-1\) contribute \(O(d^3q^{d/2})\) by counting bases. Thus the asymptotic gives actual irreducible pairs for all sufficiently large degrees; its unspecified constant alone does not settle each small degree. [Source, lines 317–349](/tmp/arxiv_nov2026/2611.18825v1/m4.tex:317)

[Q] Write \(G=H+\sigma F\), where \((\sigma,H,n,m)=(-1,N,d-1,d)\) for reflection and \((+1,h,n,n)\) for differences, and \(n,m\) are the degrees of \(F,G\). Restricting to \((F,H)=1\) costs \(O_{q,\epsilon}(q^{\epsilon n})\). Expanding \(\Lambda(G)=-\sum_{C\mid G}\mu(C)\deg C\) gives the outer weight \(-j\mu(C)\), \(j=\deg C\), and the unit progression \(F\equiv-\sigma H\bmod C\). Take \(J=\lfloor5n/6\rfloor\). For each squarefree \(C\) with \(j\le J\), Sawin's quoted estimate is
\[
 q^n/\Phi(C)+O_q(q^{(n-j)(1-\delta_q)}),\qquad
 \delta_q=\tfrac12-\log_q(352\,\mathrm e).
\]
There are at most \(q^j\) such moduli. The summed error is \(O_q(m^2q^{n-\delta_q(n-J)})\), and Sawin–Shusterman's evaluation of \(\sum j\mu(C)/\Phi(C)\) has leading term **minus** \(\mathfrak S_q(H)\). The outer minus yields \(+q^n\mathfrak S_q(H)\). The short-part error in the text is \(O_q(m^2(352\mathrm e)^{n/6}q^{11n/12}+q^{n-J/2})\). [Definitions and exact cutoff, lines 2785–2839](/tmp/arxiv_nov2026/2611.18825v1/m4.tex:2785) · [Main term, lines 2841–2862](/tmp/arxiv_nov2026/2611.18825v1/m4.tex:2841)

[Q] For \(j>J\), write \(G=BC,\ F=QZ,\ b=\deg B=m-j,\ t=\deg Q\). A second expansion, this time of \(\Lambda(F)\), switches its long divisor to its complementary divisor. The two signs multiply to plus. For \(BC=H+\sigma QZ\) and \((QZ,H)=1\) the weights are

| Range | Weight | Möbius factors varying at fixed \(B,Q,j,t\) |
|---|---|---|
| [Q] \(t\le\lfloor n/2\rfloor\) | \(j\,t\,\mu(C)\mu(Q)\) | \(\mu(C)\) |
| [Q] \(t\le\lfloor(n-1)/2\rfloor\) | \(j(n-t)\mu(C)\mu(Z)\) | \(\mu(C)\mu(Z)\) |

[P] The strict second endpoint counts the middle degree once. Since \((B,Q)=1\), choose \(Bu\equiv H\bmod Q,\ \deg u<t\) (zero representative for \(Q=1\)). Then \(C=u+QV,\ Z=\sigma(Bu-H)/Q+\sigma BV\). For reflection the monicity of \(Z\) fixes one extra coefficient. Consequently \(V=V_0+w\) with \(\deg w<\ell=j-t-(m-n)\), \(\ell\ge n/3-O(1)\). The determinant of the two affine forms is \(-\sigma H\), independent of \(V_0\). The unit conditions exclude common roots of \(C,Z\). [Two sums, lines 2864–2908](/tmp/arxiv_nov2026/2611.18825v1/m4.tex:2864) · [Parametrization, lines 2910–2938](/tmp/arxiv_nov2026/2611.18825v1/m4.tex:2910) · [Determinant, lines 3235–3249](/tmp/arxiv_nov2026/2611.18825v1/m4.tex:3235)

[Q] For one or two forms \(f_i=a_iw+b_i\) of degrees \(n_i\), Pellet's identity realizes the product of Möbius signs as \((-1)^{\sum n_i}\) times the quadratic discriminant trace on the squarefree unit locus \(U\). The proof deforms the discriminant to \(\prod_i\operatorname{Res}(f_i,f_i'+a_iv)\). CRT separates the factors on the unit locus. A root of odd multiplicity gives a nontrivial quadratic local system on a multiplicative-group factor and zero compactly supported cohomology of that fiber. The exceptional all-square locus has dimension at most \(\lfloor\ell/2\rfloor\). Hermite interpolation at marked roots and incidence comparison transfer low-degree vanishing to the zero section. With \(\kappa=\max(0,\lfloor\ell/2\rfloor-5)\), compact cohomology vanishes in degrees \(>2\ell-\kappa\). The active proof bounds the remaining Betti numbers using Bézout equations, hyperplane sections and the complete-intersection estimate. With \(r=\sum n_i,\ e=\deg H\), the trace bound is \(10^{\ell+2r+e+1}q^{3\ell/4+3}\). These are quoted geometric inputs, without an independent re-proof of the cited cohomology theorems. [Sketch, lines 423–459](/tmp/arxiv_nov2026/2611.18825v1/m4.tex:423) · [Incidence comparison, lines 2941–2976](/tmp/arxiv_nov2026/2611.18825v1/m4.tex:2941) · [Families and vanishing, lines 3030–3121](/tmp/arxiv_nov2026/2611.18825v1/m4.tex:3030) · [Affine estimate, lines 3131–3138 and 3170–3229](/tmp/arxiv_nov2026/2611.18825v1/m4.tex:3170)

[P] There are at most \(q^{m-j+t}=q^{n-\ell}\) outer pairs per degree box. Multiplying gives exponent \(n-\ell/4\le11n/12+O(1)\); the two degree weights and two degree sums cost \(O(m^4)\). The paper's \(10^{6m}\) is absorbed since \(6\log_q10<0.03<1/24\). This explains both the exponent \(23m/24\) and the role of a **fixed**, sufficiently large field. Taking \(q\) large in this theorem gives no estimate for integer Möbius signs. [Final sum, lines 3251–3262](/tmp/arxiv_nov2026/2611.18825v1/m4.tex:3251)

## 2. What reciprocal ratios give over the integers

[Q] The appendix assumes a zeta zero-free margin \(\beta<\sigma=1/2+\eta\) and a **separate** reciprocal-ratios hypothesis. At \(\Re a=\Re b=\eta\), \(|\Im a|,|\Im b|\le U^{\theta_C}\), \(k,l\le U^\nu\), its integral up to \(U\) has integrand \((l/k)^{2it}/[\zeta(1/2+a+it)\zeta(1/2+b-it)]\). The model is \(\mathbf1_{k=l}U\zeta(1+a+b)/\zeta(2+2a+2b)\), with error \(O_\epsilon(U^{1-\omega_C+\epsilon}(kl)^A(1+|\Im a|+|\Im b|)^B)\). In \(k^2m=l^2n\) a nontrivial reduced square ratio forces a square divisor in \(m\) or \(n\), killing that Möbius coefficient. The signed filter integrates to zero against the surviving diagonal. [Zero-free margin, lines 825–830](/tmp/arxiv_nov2026/2611.18825v1/m4.tex:825) · [Hypothesis and diagonal, lines 3475–3495](/tmp/arxiv_nov2026/2611.18825v1/m4.tex:3475) · [Filter, lines 3517–3528](/tmp/arxiv_nov2026/2611.18825v1/m4.tex:3517)

[Q] For each **fixed** \(h\ge1\) and fixed compactly supported smooth test at scale \(X\), the smoothed \(\mu(n)\mu(n+h)\) sum is \(O_{\Phi,h,\epsilon}(X^{1-\Delta_C+\epsilon})\), \(\Delta_C=\omega_C-2\eta>0\). Only \(k=l=1\) is needed here. For Liouville the exponent saving is \(\rho_C=\min(\nu/4,\Delta_C/[2(2A+1)])\). Truncating \(\lambda(n)=\sum_{d^2\mid n}\mu(n/d^2)\) at \(D_0=X^{\rho_C}\) costs \(O_{\Phi,h}(X/D_0)\); the ratios error costs \(O(X^{1-\Delta_C+\epsilon}D_0^{2A})\). Desmoothing gives \(O_h(X^{1-\kappa'})\) for some \(\kappa'>0\) and either coefficient, hence convergence of the corresponding \(1/n\)-weighted series with a power-saving tail. [Statements, lines 3497–3515](/tmp/arxiv_nov2026/2611.18825v1/m4.tex:3497) · [Truncation and sharp cutoff, lines 3530–3576](/tmp/arxiv_nov2026/2611.18825v1/m4.tex:3530)

[P] These conclusions concern translates with the same slope and a constant depending on \(h\). The Goldbach tail requires a prime weight and a decreasing second argument; after opening that prime weight, it requires varying opposite slopes and determinant \(N\). The square twists in the hypothesis are multiplicative frequency twists. They do not insert a reflection or a prime indicator in these conclusions. [U] No implication from this appendix to pointwise integer Goldbach was established.

## 3. The exact integer split

[P] Fix even \(N\ge4\), integer \(1\le D<N-1\), and put \(L=\log N\). Use \(1\le x\le N-2,\ (x,N)=1\); call this set \(E_N\). Omitting \(x=N-1\) costs zero in the full sum and ensures \(N-x>1\) in each part. Let \(R^\times=\sum_{x\in E_N}\Lambda(x)\Lambda(N-x)\). Use either \(w(d)=\log d\) or \(w(d)=\log(d/D)\). Since \(\sum_{d\mid m}\mu(d)=0\) for \(m>1\), both give the **exact** identity
\[
\begin{split}
 R^\times &= S_D-T_D,\\
 S_D &=-\sum_{\substack{d\le D\\(d,N)=1}}\mu(d)w(d)
       \sum_{\substack{x\in E_N\\x\equiv N\bmod d}}\Lambda(x),\\
 T_D &=\sum_{\substack{1\le k\le K\\(k,N)=1}}
       \sum_{\substack{x\in E_N,\ x<N-kD\\ x\equiv N\bmod k}}
       \Lambda(x)\mu((N-x)/k)\,w((N-x)/k),\qquad
 K=\left\lfloor\frac{N-1}{D+1}\right\rfloor . \tag{1}
\end{split}
\]
[P] The signed quantity \(T_D\) enters (1) with a minus. The bound on \(k\) uses \(d\ge D+1,\ x\ge1\); the strict endpoint is necessary even if \(k<N/D\). Equivalently a row ranges over \(D<d\le (N-1)/k,\ x=N-kd\). The prime-only version of (1) is exact with \(\Lambda(x)\) replaced throughout by \(\mathbf1_{x\ {\rm prime}}\log x\). Replacing it in any one part costs \(O_\epsilon(N^{1/2+\epsilon})\), uniformly in \(D\), by counting proper prime powers and at most \(\tau(N-x)=O_\epsilon(N^\epsilon)\) divisors, absorbing logarithms in the exponent.

[P] Möbius restricts the support to squarefree \(d\), with the additional prime or prime-power condition on \(N-kd\). There is no lower bound on the prime factors of \(d\) and no upper bound of two on their number. For example, \(N=1168,\ x=13,\ k=1,\ d=1155=3\cdot5\cdot7\cdot11>N^{5/6}\). More generally any odd squarefree \(d\) coprime to 13 gives a row with \(N=d+13,\ k=1\) for sufficiently large \(d\) and fixed \(\alpha<1\). [I] Thus the Wave 5 *zero-support* argument against a semiprime-only application does not eliminate this sum. A typical-integer distribution with uniform exceptional mass on these prime-sampled rows would be a further estimate. Unit restrictions already forbid primes dividing \(N\) in \(d\). [Wave 5 support calculation](B012_W5_LICHTMAN_SEMIPRIME_STRIKE.md)

## 4. Evaluation of the short part, uniformly in the target

[P] Write \(X=N-2\) and \(\psi(X;d,a)=\sum_{x\le X,\ x\equiv a\bmod d}\Lambda(x)\). A sufficient progression input is
\[
 L\sum_{d\le D}\max_{(a,d)=1}|\psi(X;d,a)-X/\varphi(d)|=o(N). \tag{2}
\]
The weaker signed, squarefree discrepancy actually occurring in \(S_D\) also suffices. Reinstating nonunits in the progressions costs \(N^{o(1)}\) after summing over divisors: a nonunit with positive weight is a power of a prime dividing \(N\), hence one of \(O(L^2)\) integers, and each contributes at most \(L^2\tau(N-x)\). The replacement \(X\) by \(N\) in the resulting main term costs only polylogarithms.

[P] To evaluate the main term set \(F_N(s)=\sum_{(d,N)=1}\mu(d)/(\varphi(d)d^s)=H_N(s)/\zeta(1+s)\) initially for \(\Re s>0\). For \(p\mid N\), \(H_{N,p}=(1-p^{-1-s})^{-1}\); for \(p\nmid N\), it is \((1-p^{-s}/(p-1))/(1-p^{-1-s})\). Thus
\[
 F_N(0)=0,\qquad F_N'(0)=H_N(0)=\mathfrak S(N)
 =2\prod_{p>2}\left(1-\frac1{(p-1)^2}\right)
        \prod_{\substack{p\mid N\\p>2}}\frac{p-1}{p-2}. \tag{3}
\]
The values in (3) are by continuation. The next truncation argument justifies their use with **sharp finite sums**. In particular the signed short coefficient tends to \(+\mathfrak S(N)\); no fraction \(1-\alpha\) of that main term has to be supplied by the tail.

[P] Here are uniform details. For fixed \(c>0,\ N^c\le D\le N\), write \(H_N(s)=\sum h_N(t)t^{-s}\), and take \(v=1/\log\log N\) for sufficiently large \(N\). Then \(\sum|h_N(t)|t^v\ll(\log\log N)^{O(1)}\). Indeed at \(p\nmid N\) the nonconstant coefficients are \(-1/[p^a(p-1)]\) at \(t=p^a,\ a\ge1\). At \(p\mid N\) one has the positive geometric series; split at \(p=L^2\), use \(\sum_{p\le L^2}1/p=O(\log\log L)\), \(p^v\le e^2\) there, and at most \(O(L)\) remaining divisors with \(p^{-1+v}\ll L^{-2}\). Convolve with \(\mu(m)/m\). The classical zero-free-region PNT and partial summation give \(\sum_{m\le y}\mu(m)/m=O_A((\log y)^{-A})\) and \(\sum_{m\le y}\mu(m)\log m/m=-1+O_A((\log y)^{-A})\); the constants \(0,-1\) follow from \(1/\zeta(1+s)=s+O(s^2)\). For \(t\le\sqrt D\) apply these at \(y=D/t\), allowing an extra \(O(L)\) for \(\log t\) or \(\log D\). The \(t>\sqrt D\) tail costs \(O(D^{-v/2}L^{O(1)}(\log L)^{O(1)})\) by absolute values. Hence, for either weight,
\[
 -\sum_{\substack{d\le D\\(d,N)=1}}\frac{\mu(d)w(d)}{\varphi(d)}
 =\mathfrak S(N)+O_{A,c}(L^{-A}),\qquad
 S_D=N\mathfrak S(N)+o(N)\quad\text{under (2)}. \tag{4}
\]
[P] In the centered case the additional term is \(\log D\) times the undifferentiated truncation, which is \(O_{A,c}(L^{-A})\) for every fixed \(A\). The lower bound \(\mathfrak S(N)\ge 2\prod_{p>2}(1-1/(p-1)^2)>0\) is uniform.

[Q,P] Classical Bombieri–Vinogradov (BV) supplies (2) at \(D\le\sqrt X/(\log X)^B\) for a sufficiently large fixed \(B\); also at every \(D=N^\alpha\) with fixed \(\alpha<1/2\) for large \(N\). Ordinary prime Elliott–Halberstam (EH), in its all-reduced-residues form, supplies it at every fixed \(\alpha<1\) (use a slightly larger fixed level to absorb endpoints). If EH is formulated for the prime Chebyshev weight, apply that version directly to the prime-only identity. On the required residue \(a=N\), the **summed actual** prime-power correction to the short part is \(N^{1/2+o(1)}\) by the divisor count above. ERH's individual square-root errors summed by absolute values give \(O(D\sqrt N\,L^{O(1)})\), which by itself gives no level \(5/6\). Pascadi's \(5/8-\epsilon\) progression result quoted in this repository assumes special modulus weights and residue conditions. Smooth truncation of \(\mu(d)\log d\) does not establish those conditions at the growing residue \(N\). The cached Nov. 2026 unbalanced-convolution result has different coefficient hypotheses again. [Pascadi progression hypotheses in the local audit](B012_BILINEAR_PARITY_ATTACK.md) · [Nov. 2026 convolution comparison](B004_W5_LEE_GWX_PASCADI_STRIKE.md)

### A support test on genuine primes

[P] One can verify more than nonempty support. Fix \(1/2<\alpha<1,\ D=\lfloor N^\alpha\rfloor,\ K_0=\lfloor N/(3(D+1))\rfloor\). Take \(x=p\in[N/4,N/2]\) prime, \((p,N)=1,\ k\mid N-p,\ k\le K_0\). All rows have odd \(k\), and \(d=(N-p)/k>D\). Give a row weight \(\log p\). For any fixed number of disjoint bands
\[
 \exp(L^{a_i})<\ell\le\exp(L^{b_i}),\qquad
 0<a_1<b_1<a_2<b_2<\cdots<a_j<b_j<1,
\]
the relative mass of rows with a prime factor of \(d\) in **each** band tends to one. At least \(1/2-o(1)\) of all rows have that property **and squarefree \(d\)**. Both statements hold as averages over the indicated \(k\), uniformly in the even target; they also hold for each fixed admissible \(k\) as \(N\) grows through \((k,N)=1\).

[P] Here are the details. The reference mass is \(M=(N/4)\sum_{k\le K_0,(k,N)=1}1/\varphi(k)\ge N/4\), and BV gives actual mass \(M+o(N)\). In a single band count divisors \(\ell\mid d,\ \ell\nmid kN\). Relative to the main term for row \(k\), the first and distinct-pair densities from the progressions modulo \(k\ell,\ k\ell_1\ell_2\) are \(1/(\ell-1)\) and the product of these densities. Write \(h_k=\sum_{\ell\ {\rm in\ band},\,\ell\nmid kN}1/(\ell-1)=(b_i-a_i)\log L+O(1)\) by Mertens and the \(O(L)\) prime divisors of \(kN\). The summed second moment about \(h_k\) is \(O(M\log L)+o(N)\): its diagonal main term is at most \(h_k\) per unit of row mass and the off-diagonal main terms cancel after centering. Indeed all moduli are \(\le K_0\exp(2L^{b_j})\le N^{1/2-c_\alpha}\) for some \(c_\alpha>0\). Grouped BV errors have multiplicity at most a threefold divisor function, times a fixed log power from centering. For clarity, if \(E(m)\) is the maximal absolute progression discrepancy at these endpoints, Cauchy–Schwarz bounds \(\sum\tau_3(m)E(m)\) by \((\sum E)^{1/2}(\sum\tau_3^2 E)^{1/2}\). BV saves arbitrary log powers in the first factor and \(E(m)\ll NL/m,\ \sum_{m\le N}\tau_3(m)^2/m\ll L^{O(1)}\) suffice in the second. Thus the zero-hit mass costs \(O(M/\log L)\) per band. A finite union costs \(o(M)\).

[P] For squarefreeness, \(d\) is odd on these rows for large \(N\). For odd \(\ell\le L^3,\ \ell\nmid N\), the row density of \(\ell^2\mid d\) is \(\varphi(k)/\varphi(k\ell^2)\le1/[\ell(\ell-1)]\), with negligible summed progression error by the same BV argument. Primes dividing \(N\) cannot divide \(d\). The sum of the majorants is at most \(\sum_{m\ge3}1/[m(m-1)]=1/2\). For \(\ell>L^3\), drop primality and count multiples in \(1\le d\le N/k\). Their weight per \(k\) is \(O(L[N/(kL^3)+\sqrt{N/k}])\), whose sum is \(o(N)\). This proves the assertion; with \(k\) fixed the same proof uses just its own progression errors. This test proves neither cancellation between the two squarefree signs nor typicality at every moving endpoint. Even full occupancy of finitely many bands says nothing about the parity of the total number of prime factors.

## 5. The precise budget for the long part

[P] Let \(P_N^\times\) denote the contribution to \(R^\times\) in which at least one input is a proper prime power. Then \(0\le P_N^\times\ll\sqrt N L^2\): there are \(O(\sqrt N)\) such powers \(\le N\), counting the squares first and the at most \(O(N^{1/3}L)\) higher powers. For the uncentered or centered \(T_D\), the exact criterion for a unit prime pair is \(T_D<S_D-P_N^\times\). A nonunit prime pair can occur only at \(N=2p\), which already has the pair \(p+p\). Consequently under (2) the following **one-sided aggregate hypothesis** suffices for positive linear prime-pair weight at every sufficiently large even target:
\[
 \boxed{\quad \limsup_{\substack{N\to\infty\\2\mid N}}
       \frac{T_D(N)}{N\mathfrak S(N)}<1 .\quad} \tag{5}
\]
[P] Uniform \(T_D=o(N)\) yields the full main term with absolute \(o(N)\) error under (2), and conversely that main term plus (4) gives \(T_D=o(N)\). Positivity alone needs only the exact strict inequality above and allows a shrinking margin if it exceeds the actual errors. A fixed margin in (5) is convenient, not necessary. A theorem with an asymptotic threshold would still need an effective bridge through the remaining finite targets for **all** \(N\ge4\). At a BV cutoff, proving (5) needs no EH assumption. At \(5/6\) or \(1-\epsilon\) it needs the corresponding short estimate, for which prime EH suffices. If an effective tail bound is proved at some cutoff beyond BV, a matching short estimate is still required there.

[P] To price a proposed **rowwise** theorem set \(U_k=(N-1)/k\) and define
\[
 M_k=\sup_{D\le y\le U_k}
 \left|\sum_{\substack{y<d\le U_k\\N-kd\in E_N}}
      \Lambda(N-kd)\mu(d)\right|.
\]
With \(y=D\) included, summation by parts and monotonicity give
\[
 |T_D|\le \sum_{\substack{k\le K\\(k,N)=1}} w(U_k)M_k. \tag{6}
\]
Indeed \(w(d)=w(D)+\int_D^d dt/t\) on the long side for both weights, with \(w(D)\ge0\). This formula retains the endpoint range even when \(U_k\) is not integral. It needs uniformity in the moving inner intervals, or else a bound directly on the weighted aggregate. There is no need to maximize over \(N\) *inside* the sum over \(k\); it suffices that the resulting bound hold at every even \(N\).

[P] If a proposed uniform bound is \(M_k\le C\,N/(\varphi(k)L^s)\), the exact coefficient in this majorization is \(C L^{-s}\sum_{k\le K,(k,N)=1}w(U_k)/\varphi(k)\), in units of \(N\). For \(D=N^{\alpha+o(1)}\) with fixed \(0<\alpha<1\), dropping the coprimality restriction gives, respectively,
\[
 \sum_{k\le K}\frac{\log U_k}{\varphi(k)}
    =\bigl(C_\varphi(1-\alpha^2)/2+o(1)\bigr)L^2,\qquad
 \sum_{k\le K}\frac{\log(U_k/D)}{\varphi(k)}
    =\bigl(C_\varphi(1-\alpha)^2/2+o(1)\bigr)L^2. \tag{7}
\]
Here \(C_\varphi=\prod_p(1+1/[p(p-1)])\). For example \(k/\varphi(k)=\sum_{r\mid k}\mu^2(r)/\varphi(r)\) gives \(\sum_{k\le u}1/\varphi(k)=C_\varphi\log u+O(1)\) by harmonic summation; \(\sum_r\mu^2(r)\log(2r)/(r\varphi(r))\) converges. Partial summation gives (7). On \(N=2^j\) restricting to odd \(k\) replaces \(C_\varphi\) by a positive constant (the Euler residue loses the \(p=2\) local series \(1+\sum_{a\ge1}1/\varphi(2^a)=3\)). Thus the **two-log cost of this majorant** is real even with admissibility enforced. It is not a lower bound on the true signed tail.

| Short cutoff | Cofactor range (up to rounding) | Raw / centered coefficients in (7), in units of \(C_\varphi L^2\) | Short-side input |
|---|---|---|---|
| [P] \(N^{5/6}\) | \(N^{1/6}\) | \(11/72,\ 1/72\) | (2) at this level, e.g. prime EH |
| [P] \(N^{1-\epsilon}\), fixed \(\epsilon>0\) | \(N^\epsilon\) | \(\epsilon-\epsilon^2/2,\ \epsilon^2/2\) | prime EH for fixed \(\epsilon\) |
| [P] \(\sqrt X/(\log X)^B\) | \(\asymp\sqrt N L^B\) | \(3/8,\ 1/8\) | unconditional BV for suitable \(B\) |

[P] For fixed \(\alpha\), \(s>2\), or a uniform little-oh at \(s=2\), is sufficient for \(o(N)\) by (6). At \(s=2\) a sufficiently small constant already gives (5); for a fixed row the analogous sufficient saving is little-oh of one inverse logarithm. These thresholds refer to unweighted Möbius sums **with the prime already weighted by \(\log p\)**. In a central interval the unweighted prime count has size \(N/(\varphi(k)L)\); a saving \(L^{-s}\) relative to that count still gives \(s\), not \(s+1\), after restoring the prime weight. A row theorem allowing losses \(k^\epsilon\), constants depending arbitrarily on \(k,N\), or exceptional even targets does not give (6) with this budget. Direct signed averaging over \(k\) need only give (5), and can avoid both absolute-value losses.

[P] For the centered weight at a variable cutoff write \(H=\log(N/D)\). The corresponding unrestricted envelope is \(O(1+H^2)\), by the same summation, compared with \(O(L(1+H))\) for the raw weight. Thus a hypothetical reflected saving \(L^{-s}\) with \(H=o(L^{s/2})\) would suffice in the centered calculation. Ordinary EH at every **fixed** level does not provide (2) at a prescribed \(D=N\exp(-L^\gamma)\), nor does it give constants uniform as \(\epsilon\downarrow0\). At either fixed \(5/6\) or fixed \(1-\epsilon\), centering improves the coefficient and leaves the log exponent at two. A bounded smooth partition \(V(d/D)+(1-V(d/D))=1\), with \(V=1\) below 1 and zero beyond a fixed factor, reassigns only a transition interval. Partial summation gives the same orders for a fixed bounded-variation profile. Smoothing does not change the sign information needed on the interior. These are budgets for specified estimates, without any impossibility claim for other decompositions.

## 6. Integer affine forms and the determinant

[P] A direct geometric analogue is available at the level of the equations. In (1) put \(Y=\lfloor\sqrt N\rfloor\). For \(x=N-kd=qz\),
\[
 \Lambda(x)=-\!\!\sum_{qz=x,\ q\le Y}\!\mu(q)\log q
             -\!\!\sum_{qz=x,\ z>Y}\!\mu(z)\log z. \tag{8}
\]
In the second sum \(q\le Y\) automatically. Each original divisor occurs once by whether it exceeds \(Y\). Thus the contribution of \(-T_D\) is the **sum with plus signs** of \(w(d)\mu(d)\mu(q)\log q\) and \(w(d)\mu(d)\mu(z)\log z\) over the respective ranges. The unit restriction forces \((kq,N)=1\) and \((k,q)=1\), since a common divisor of \(k,q\) divides \(kd+qz=N\). Fix \(k,q\); choose \(0\le u<q\) with \(ku\equiv N\bmod q\) (take \(u=0\) at \(q=1\)). The two affine forms and their determinant are exactly
\[
 d=u+qt,\quad z=v-kt,\quad v=(N-ku)/q,\qquad
 qv-(-k)u=N .
\]
[P] Keep \(d>D,\ z\ge1,\ qz\in E_N\), and also \(z>Y\) in the second sum. Before the coprimality test these give intervals in \(t\), with \(O(1+N/(kq))\) candidates; near a boundary they may be much shorter. The forms are primitive and on unit rows \((d,z)=1\). The one-form sum varies \(\mu(d)\); the two-form sum varies \(\mu(d)\mu(z)\) on the same progression. The factor \(N\) in the determinant survives changing the representative \(u\) or translating \(t\).

**[U] A sufficient integer substitute for the geometric estimate.** For fixed \(\alpha>1/2\), suppose for some fixed \(0<\delta<1\) and for every allowed \(N,k,q\) the following holds on every subinterval \(I\) of the above parameter interval, including the one-form unit condition:
\[
 \left|\sum_{\substack{t\in I\\(qz,N)=1}}\mu(d)\right|
 +\left|\sum_{\substack{t\in I\\(qz,N)=1}}\mu(d)\mu(z)\right|
 \ll_\alpha (1+N/(kq))^{1-\delta}. \tag{9}
\]
[P] The scale on the right is the full row scale, so (9) asks for no relative saving on tiny intervals. Each log weight, or product of two such weights, has supremum plus total variation \(O(L^2)\) on the permitted interval (use the product rule and monotonicity of each log). Under (9), (8) and summation by parts give
\[
 |T_D|\ll_{\alpha,\delta} L^2
 N^{1-\delta}\!\sum_{k\le N/D} k^{-1+\delta}
                  \sum_{q\le\sqrt N} q^{-1+\delta}
 \ll_{\alpha,\delta} L^2 N^{1-\delta(\alpha-1/2)}
\]
for \(D=\lfloor N^\alpha\rfloor\). Indeed \(N/(kq)\gg N^{\alpha-1/2}\). At \(5/6\) the saving is \(\delta/3\), and at \(1-\epsilon\) it is \(\delta(1/2-\epsilon)\). Dependence on a fixed \(\delta\) is allowed; a fixed power cost in \(N\) can destroy the saving. At BV's cutoff \(N/(kq)\) can be \(O(1)\) or smaller, so this particular absolute-sum proof gives no power saving there. The aggregate hypothesis (5) stays meaningful. [I] Equation (9) isolates the arithmetic work performed by the discriminant argument. The weaker (5) isolates only what Goldbach positivity consumes.

## 7. Comparison of possible inputs

- **[Q,P] Lichtman and Lü–Wang–Wu.** The cached theorem states a relative \(L^{-1/2+\epsilon}\) saving for \(\sum_{p\le X}\mu(p+2)\); the earlier result quoted there is qualitative \(o(\pi(X))\). Even granting the same exponent hypothetically at every reflected row and every endpoint gives \(O(NL^{3/2+\epsilon})\) through (6) for fixed \(\alpha\), or \(O(NL^{1/2+\epsilon})\) on the \(k=1\) envelope. These are deficits against \(o(N)\) of this **rowwise argument**. The actual theorem gives neither of these reflected estimates. Wave 5's equality-of-cofactors calculation applies already at \(k=1\), and at common fixed \(k\) the \(k\)'s cancel in \((N-mn)/(ka)=(N-rs)/(kb)\). Thus \(bmn-ars=N(b-a)\), whereas the published cutoff has \(bmn-ars=a-b,\ |a-b|\le3Y_1\) at \(a,b\in[Y_1,4Y_1]\), \(Y_1=N^{o(1)}\). For distinct \(a,b\) the reflected determinant has magnitude at least \(N\). This is a second, different determinant calculation from \(qv+ku=N\) in (8). Diagonal \(a=b\) terms cannot handle the off-diagonal terms. Averaging the cofactor while keeping the target fixed does not itself give an estimate on either family. [Lichtman, lines 105–121](/tmp/arxiv_nov2026/2611.28392v1/binary_chowla1.tex:105) · [Cofactor equality and cutoff, lines 984–998 and 1042–1057](/tmp/arxiv_nov2026/2611.28392v1/binary_chowla1.tex:1042) · [Wave 5 determinant](B012_W5_LICHTMAN_SEMIPRIME_STRIKE.md)
- **[P,U] ERH and prime EH.** ERH controls individual Dirichlet zero locations. Prime EH supplies the unweighted progression input (2). Neither quoted estimate controls the sign of \(\mu((N-x)/k)\) against prime \(x\), even for \(k=1\). EH can count additional divisibility tests as in the support calculation, but the signed correlation (5) still needs an estimate. No logical independence of conjectures is asserted.
- **[P,U] Chowla.** Fixed-shift two-point Chowla, even with a fixed-shift power saving as in the conditional GWX appendix, supplies neither the opposite slopes and determinant in (9) nor the weighted sum in (1). A version for fixed affine forms with constants depending on those forms would still leave uncontrolled a triangular array with determinant growing like \(N\). Averages over shifts or logarithmically weighted averages do not in themselves give the required pointwise natural-scale inequalities.
- **[Q,P] GWX Hypothesis 1.1.** The primitive Dirichlet \(2/2\) ratios hypothesis asks for conductor-uniform error \(O_{\eta,\epsilon}(q^{1-\omega_D+\epsilon}(1+T)^B)\), all conductors including composite, numerator real parts \(1/2\), denominator real parts \(1/2+\eta\), and \(T\le100\log(2q)\); \(\omega_D>0\) is independent of small fixed \(\eta\). GWX's integer theorem assumes **Dirichlet GRH as well** and yields \(R=N\mathfrak S(N)+O_\epsilon(N^{1-\omega_D+\epsilon})\). Thus their conjunction and (4) at the unconditional BV cutoff imply \(T_D=o(N)\) there by subtraction (the deleted nonunit part is \(N^{o(1)}\)). With EH the same inference is valid at \(5/6\). This logical implication gives no proof of (9), no termwise row estimates, and no converse from (5) to ratios. Hypothesis 1.1 alone is not the assumption of the quoted theorem. [Hypothesis, lines 146–177](/tmp/arxiv_nov2026/2611.18825v1/m4.tex:146) · [Goldbach theorem, lines 235–252](/tmp/arxiv_nov2026/2611.18825v1/m4.tex:235)

**[P] Finite identity check.** The scratch program expanded every logarithm in the ordered prime-log basis and compared integer coefficient dictionaries for the direct convolution, the progression split and the affine switch. It included both weight conventions, square endpoints and nonunit exclusions. The requested interpreter reported “586 exact coefficient comparisons passed for even targets 4 through 300” in under one second. This tests (1) and (8) on finite instances. [Replay script](/tmp/astra_w6_2a/check.py)

**[U] Verdict for B-005.** The integer support admits typical squarefree quotients. The algebra, the short main term and the determinant all transfer. The function-field cancellation theorem has no established integer replacement in the sources examined. A complementary signed upper bound (5) with the BV cutoff would give eventual Goldbach unconditionally; proving (9) with a matching prime progression estimate would give the full eventual main term. Binary Goldbach remains open, including under ERH.

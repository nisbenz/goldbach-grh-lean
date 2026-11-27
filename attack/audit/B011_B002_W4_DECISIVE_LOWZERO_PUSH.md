# How little of the zero-pair sum suffices for pointwise Goldbach?

[Q] Wave 4, 27 November 2026, astra-w4-lowzeros. Assume Dirichlet ERH for every primitive character, including zeta. [Q] marks a sourced input, [P] a derivation, [I] an interpretation and [U] an unproved estimate. The analysis is asymptotic as the even integer \(N\) tends to infinity. It has no Lean checker verdict.

[P] On canonical Farey cells of order \(\asymp\sqrt N\), the H2 complementary pole square is \(O_\epsilon(N^{1+\epsilon}/H)=o(N)\). A uniform \(O(N/H)\) is false. The residue and all its interactions are \(o(N)\). The mixed pole–zero term on \(q\mid N\) is also \(o(N)\). On the other denominators, character orthogonality still spends order \(N\) before logarithms. [U] I do not have \(o(N)\) for that particular mixed term.

[P] **Increasing the order to \(N^{2/3}\) eliminates the whole mixed term**, even with absolute values inside the integral. On this dissection the remaining signed statistic uses \(Q/\log^4 N<q\le Q\), inducing conductors \(d\ge q/\log^2 N\), and ordinates \(|\gamma|<2\log\log N\). The pairs can also be restricted to distinct characters with product conductor above \(Q^{1/2-\delta}\) for fixed \(0<\delta<1/2\). Formula (12) evaluates the fields at \(\beta=0\). The difference between \(N\) times this statistic and the *original square-root-order* \(I_{\rm low}(N)\) is \(o(N)\). A one-sided lower bound for the statistic implies Goldbach for all sufficiently large even integers. [U] Its sign is open. [P] The actual low-zero field has squared norm \(\gg N\log N\) on the H2 complement.

## 1. Cells, explicit formula and two norm estimates

[Q] Write \(L=\log N\), \(C=4\cdot10^{18}\), \(H=\lfloor2(N/C)^{1/16}\rfloor\), \(T_y=(17/4)(N/C)^{1/16}\), \(B=\mathbb T\setminus A_y\), and \(e(t)=e^{2\pi it}\). The major arcs have half-width \(T_y/(2\pi N)\). Write \(S(\alpha)=\sum\Lambda(n)e^{-n/N}e(n\alpha)\). [H2 and the prime-power allowance](../../proof/strong_goldbach_research.md) · [Primitive Mellin formula](../../proof/weak_goldbach_proof.md) · [Wave 3, especially (3)–(5)](B011_W3_PERSISTENT_BETA_PUSH.md)

[P] Specify a dissection, since the individual terms depend on it. Use the mediants between consecutive order-\(Q\) Farey fractions as boundaries, periodically across zero. The two positive half-lengths at \(a/q\) are
\[
 w^\pm_{q,a}={1\over q(q+r_\pm)},\qquad Q-q<r_\pm\le Q,\qquad
 r_-\equiv a^{-1},\quad r_+\equiv-a^{-1}\pmod q .
 \tag{1}
\]
These follow from the neighbor determinant one and the mediant formula. At \(q=1\) use its two actual neighbors. Thus \(1/(2qQ)\le w^\pm\le1/(qQ)\). Write \(\ell_{q,a}=w^++w^-\), \(u=2\pi N\beta\), \(z=(1-iu)/N\) and \(U_q=2\pi N/(qQ)\). At either order used for H2, \(T_y H Q=o(N)\), so every H2 major arc is entirely inside its own cell for sufficiently large \(N\). Every cell with \(q>H\) is in \(B\) up to endpoints. Wave 3 allowed arbitrary ties. The estimates below that complete signed sums at the boundaries use (1).

[P] With \(\chi^*\) inducing \(\chi\bmod q\), let \(c_\chi=\tau_q(\bar\chi)/\varphi(q)\), \(F_\chi=\sum_\rho\Gamma(\rho)z^{-\rho}\) for primitive \(\chi\), and \(Z=\sum_\chi c_\chi\chi(a)F_{\chi^*}\). Write \(Z_{<t}\) for the part restricted to \(|\gamma|<t\), with multiplicities. Finite Fourier inversion and the primitive Mellin formula give
\[
 S=M-Z+R,\qquad M={\mu(q)\over\varphi(q)z},\qquad
 \sum_\chi|c_\chi|^2=1 .                                      \tag{2}
\]
For \(Y=L^4\), the six terms of \(S_{<Y}^2\) are \(M^2,-2M Z_{<Y},Z_{<Y}^2,2MR,-2Z_{<Y}R,R^2\). The signed functional uses \(e(-N\alpha)\) for every term.

[P] Uniformly for \(Q\asymp N^\theta\) with fixed \(0<\theta<1\), one has \(\|R\|_\infty\ll(1+\sqrt Q)L^2\). Deleting prime powers supported on primes dividing \(q\), and restoring the nonunits, costs \(O((1+\sqrt q)L^2)\) by the companion character expansion. The primitive residue at zero is \(O(\log(2d)+|\log z|+1)\). On the shifted line \(\Re s=-1/2\), Stirling gives \(|\Gamma(s)|\ll(1+|t|)^{-1}e^{-\pi|t|/2}\). The functional equation there gives \(|L'/L|\ll\log(2d(2+|t|))\). Integrating against \(e^{-c|t|/(1+|u|)}\) costs \(O(|z|^{1/2}L^2)\), by splitting at \(1\) and \(1+|u|\). Here \(|z|\ll1\), and the character coefficients have absolute sum at most \(\sqrt q\). The shifted integral includes the remaining trivial-zero contribution. This uses the primitive Mellin proof for general polynomial \(d\) and \(u\), without extending its square-root-order numerical constant. [Bounds for the shift and induction](../../proof/binary_goldbach_exceptional_proof.md)

[P] Let \(E_q\) be the energy of \(Z\) on all cells of denominator \(q\), or that of any field restricted to a fixed set of ordinates per character. Then
\[
 E_q\ll \varphi(q) U_q L^2,\qquad
 \sum_{q\le D} E_q\ll {N D\over Q}L^2,\qquad
 \sum_{q\mid N,\ q\le Q}E_q\ll {N\over Q}\tau(N)L^2 .        \tag{3}
\]
For \(U_q\le1\), \(|F_{\chi^*}|\ll\sqrt N L\) by gamma decay and the unit-interval zero count. Enlarge each interval to the common interval and use character orthogonality in the nonnegative square. For \(U_q>1\), Wave 3 (4) gives single-character shell norm \(\ll\sqrt T\log(2dT)e^{-cT/V}\) for height \(T\le|\gamma|<2T\), \(V\le|u|\le2V\). Its integration-by-parts and absolute row-sum proof permits restricted zero sets. Summing dyadic norms at fixed \(V\) gives \(O(\sqrt V L)\), since \(V\) is polynomial in \(N\). Bounded heights, including \(\gamma=0\), cost \(O(L)\) per shell. Sum the squared norms over disjoint shells to obtain (3). The steps in this argument apply to any admissible cell subsets.

[P] Parseval and the prime number theorem give \(\|S\|_2^2\sim NL/2\). Extending the model integral at each center to the line gives
\[
 \|M\|_2^2\le {N\over2}\sum_{q\le Q}{\mu^2(q)\over\varphi(q)}
       ={N\over2}(\log Q+O(1)).
\]
The divisor-sum asymptotic is derived in Wave 3. By (3), \(\|Z_{<Y}\|_2\ll\sqrt N L\). Consequently \(2MR,-2Z_{<Y}R,R^2\) together cost \(O(\sqrt{NQ}L^3+QL^4)=o(N)\), even in absolute value, for either order below. The same bound holds for all ordinates together.

## 2. The signed pole square and the failure of a uniform \(O(N/H)\)

[P] Put \(a_q(N)=\mu^2(q)c_q(N)/\varphi(q)^2\), where \(c_q(N)\) is a Ramanujan sum, \(D_H=\sum_{q\le H}a_q(N)\), and \(\mathfrak S(N)=\sum_{q\ge1}a_q(N)\). We use two uniform estimates, valid for every \(\epsilon>0\) and \(1\le K\le N\),
\[
 \sum_{q>K}|a_q(N)|\ll_\epsilon N^\epsilon/K,\qquad
 \sum_{q\le N}q|a_q(N)|\ll_\epsilon N^\epsilon .            \tag{4}
\]
Indeed split squarefree \(q=db\) with \(d\mid\operatorname{rad}(N)\) and \((b,N)=1\). The absolute weight is \(1/(\varphi(d)\varphi(b)^2)\). Use \(\sum_{b>x}1/\varphi(b)^2\ll_\eta x^{-1+\eta}\) for \(x\ge1\), and bound \(d/\varphi(d),\tau(N)\) by arbitrarily small powers of \(N\). For the second estimate sum \(b/\varphi(b)^2\) up to \(N\). The same argument gives \(|D_H|\ll_\epsilon N^\epsilon\).

[P] For \(Q=\lfloor\sqrt{2\pi N}\rfloor\), the canonical cell model satisfies
\[
 \Re\int_B M^2 e(-N\alpha)d\alpha
   ={N\over e}\mathfrak S(N)-N J(T_y)D_H(N)
       + O_\epsilon(N^{3/4+\epsilon}).                      \tag{5}
\]
Here \(J(T)=(2\pi)^{-1}\int_{-T}^T e^{-iu}(1-iu)^{-2}du\) and \(J(\infty)=1/e\). Extend the cell at each center to the real line. At fixed \(\beta\) on either side, the omitted centers are empty until \(|\beta|\ge1/(2qQ)\). Formula (1) makes their inverses a cyclic interval of residues, possibly full. Finite Fourier completion of its indicator costs \(O(\log(2q))\) in normalized coefficient absolute sum, by the geometric-series bound. The classical Weil–Estermann bound for the complete Kloosterman sum is \(\tau(q)q^{1/2}(q,N,m)^{1/2}\) at inverse frequency \(m\), also valid at \(m=0\). Thus the integral error at denominator \(q\) is
\[
 \ll {\mu^2(q)\over\varphi(q)^2}\, qQ\,
        \tau(q)\sqrt{q(q,N)}\log(2q).
\]
We used \(\int_{|\beta|\ge1/(2qQ)}|z|^{-2}d\beta\ll qQ\). Summation gives \(O_\epsilon(Q^{3/2}N^\epsilon)\), since \(\sum_{q\le Q}(q,N)^{1/2}/\sqrt q\ll\sqrt Q\,\tau(N)\) by summing over common divisors. The full-line coefficient is \(N/e\) times the Ramanujan weight. Use (4) for \(q>Q\), and subtract the exact H2 model on \(A_y\). This proves (5) including the boundaries.

[P] Integration by parts against \(e^{-iu}\) gives \(|J(T)-1/e|\ll T^{-2}\) for \(T\ge1\). Since \(H\asymp T_y\asymp N^{1/16}\), (4) and (5) imply \(O_\epsilon(N^{1+\epsilon}/H)=o(N)\).

[P] **A uniform constant times \(N/H\) fails.** Let \(m\) run through primorials including 2, set \(X=C(m/4)^{16}\), and average over multiples \(N=mk\) in \([X,2X]\). There are \(\asymp X/m\) such \(k\), and \(H\) lies between \(m/2-O(1)\) and \(0.53m\). In the tail \(\sum_{q>H(N)}a_q(N)\), truncate at \(W=X^{1/4}\) using (4), at cost \(o(1/m)\). Write squarefree \(q=db\), now with \(d\mid m\) and \((b,m)=1\). Its weight is \(c_b(k)/(\varphi(d)\varphi(b)^2)\). For \(b>1\) the eligible \(k\)'s form an interval, because \(H(mk)\) is monotone. On any such interval the sum of \(c_b(k)\) is \(O(\sigma(b))\), by \(c_b(k)=\sum_{h\mid(b,k)}h\mu(b/h)\) and cancellation of the interval-length terms. The total error **in the average** is
\[
 \ll {m\over X}\sum_{d\mid m}{1\over\varphi(d)}
                \sum_{b\le W}{\sigma(b)\over\varphi(b)^2}
     \ll_\epsilon {m\over X}X^\epsilon=o(1/m).
\]
The \(b=1\) terms are nonnegative and \(q=m\) always contributes \(1/\varphi(m)\). Replacing \(J(T_y)\) by \(1/e\) in (5) costs \(o(N/m)\). Therefore some targets in each block have complementary pole coefficient divided by \(N\) at least \(1/(e\varphi(m))-o(1/m)\). Since \(m/\varphi(m)\to\infty\), the proposed uniform \(O(N/H)\) cannot hold.

[P] For \(Q=\lfloor N^{2/3}\rfloor\), (5) holds with error \(O_\epsilon(N^{2/3+\epsilon})\) by a simpler argument. Replace each cell by its full common interval of radius \(1/(qQ)\). By (1) the added length at each end is at most \(1/Q^2\). Its total absolute pole-square cost is \(O(N^2\log(2Q)/Q^2)\). Extending those common intervals to the line then costs \(O(Q\sum_{q\le Q}q|a_q(N)|)\), and (4) handles the remaining series tail. This proves \(o(N)\) on H2 at the enlarged order. For H1 the two major arcs instead contribute \(2NJ(17/4)\), leaving the arithmetic main term \(N(\mathfrak S(N)/e-2J(17/4))\) on their complement up to \(o(N)\).

### Why the original arbitrary tie rule matters

[P] At \(Q=\lfloor\sqrt{2\pi N}\rfloor\), the pole square need not be \(o(N)\) uniformly over the measurable assignments allowed in Wave 3. In fact two admissible assignments can differ in its real complementary coefficient by \(\gg N\). Take \(0.9Q<q,r\le Q\) with \(q\) odd squarefree, \(4\mid r\) and \((q,r)=1\). Each ordered pair gives one consecutive Farey gap \(a/q<b/r\), since \(bq-ar=1\) and \(q+r>Q\). There are \(\gg Q^2\) such gaps. For a direct count, impose the restrictions at primes up to a fixed \(P\) by CRT. At odd \(p\) the permissible density is \(1-2/p^2+1/p^3\); the factor at 2 is \(1/8\). The product is positive. Pairs violating squarefreeness or coprimality at a larger prime cost \(O(Q^2\sum_{n>P}n^{-2})\), so take \(P\) large and then \(Q\) large.

[P] In each gap the entire interval \(1/3\le u=2\pi N(\alpha-a/q)\le2/3\) is covered by both Dirichlet windows. Indeed the overlap starts at \(2\pi N(1/(qr)-1/(rQ))<1/3\) and ends at \(2\pi N/(qQ)>2/3\). This interval is in \(B\). The \(r\)-pole vanishes; the \(q\)-pole is nonzero. Choose between the two assignments according to the sign of \(\Re[e(-Na/q)e^{-iu}(1-iu)^{-2}]\), and reverse the choice for the second assignment. Outside these intervals use identical cells. The integral of the absolute real part of the displayed factor in \(u\) is bounded below by an absolute constant uniformly in the initial phase: the continuous function \(2\arctan u-u\) is strictly increasing here, and compactness in the initial phase gives a positive minimum. The difference per gap is therefore \(\gg N/\varphi(q)^2\). Summing gives \(\gg N\). At least one assignment has magnitude \(\gg N\). Wave 3 controls their **total truncated coefficients** irrespective of the assignment; individual pole coefficients have no such invariance. Formula (5) specifies exactly the geometric choice to which it applies.

## 3. The mixed term at the two orders

[P] Let \(G_q(\chi;n)=\sum_a^*\chi(a)e(na/q)\). For squarefree \(q=dr\) with \(\chi\) induced from the primitive \(\psi\bmod d\), CRT and the primitive Gauss identity give
\[
 \tau_q(\bar\chi)G_q(\chi;-N)
     = d\,\mu(r)c_r(N)\bar\psi(N).                           \tag{6}
\]
Indeed the local additive characters use \(r^{-1}\bmod d\) and \(d^{-1}\bmod r\), the two character factors at \(r\) cancel, and \(\tau_d(\psi)\tau_d(\bar\psi)=\psi(-1)d\). The convention extends primitive characters by zero on nonunits. On a common \(\beta\)-window the exact mixed integrand after the center sum, apart from \(e(-N\beta)/z\), is therefore
\[
 \sum_{dr=q}{\mu(d)d\,c_r(N)\over\varphi(q)^2}
       \sum_{\psi\bmod d}^{\rm primitive}\bar\psi(N)F_{\psi,<Y}(\beta).
                                                                    \tag{7}
\]
For all windows one instead inserts \(1_{B\cap{\rm cell}(q,a)}(a/q+\beta)\) inside \(G_q\). On the H2 cells (1) its additional endpoint modes are twisted sums with the phase \(e((-Na+m a^{-1})/q)\). Dropping that mask would change the statistic.

[P] For \(q\mid N\) the complete \(G_q\) vanishes except for the principal character. Even without completing anything, the contribution of **all divisor cells** to \(\int_B|MZ_{<Y}|\) is \(O(\sqrt N\,L\sqrt{1+Y}\,\tau(N))=N^{1/2+o(1)}\). To see this, at each fixed \(\beta\) enlarge the nonnegative sum over centers. Orthogonality and Cauchy give
\(\sum_a^*|Z_{<Y}|\le\varphi(q)\max_\psi|F_{\psi,<Y}|\).
Gamma decay and the zero count give
\[
 |F_{\psi,<Y}|\ll \sqrt N(1+|u|)^{-1/2}
                        \min(1+Y,1+|u|)\,L .                \tag{8}
\]
After multiplication by \(|M|\) and integration in \(u\), the integral of
\((1+|u|)^{-3/2}\min(1+Y,1+|u|)\) is \(O(\sqrt{1+Y})\). This accounts for the unequal windows as well.

[P] For \(q\nmid N\) with a common factor with \(N\), the magnitude of \(G_q\) can equal \(\sqrt d\,\varphi(r)\) if \(r\mid N\) and \((d,N)=1\). A uniform \(O(\sqrt q)\) for imprimitive twists is false. Even in the coprime primitive case, taking \(d=q\) in (7) leaves \(q/\varphi(q)^2\) multiplying a sum of \(\varphi^*(q)\) zero fields with phases \(\bar\psi(N)\). Here \(\varphi^*(q)\) counts primitive characters. For squarefree \(q\asymp\sqrt N\) with \(\varphi^*(q)\asymp q\), this costs order one times the size of one field. Integration of \(z^{-1}F_{\psi,<Y}\) on \(|u|\ll1\) allows \(O(\sqrt N L)\) per denominator. Summing the denominators gives power \(N^1\).

[P] This loss already occurs in the **input inequalities** on a common central subinterval. For \(N=2^k\), a positive proportion of \(q\in(Q/2,Q]\) are odd squarefree with \(\varphi^*(q)=\prod_{p\mid q}(p-2)\gg q\). Indeed odd squarefrees have positive density and the mean of \(\sum_{p\mid q}1/p\) is bounded, so restrict to a sufficiently large fixed upper bound on that sum. In (7), bounded abstract primitive amplitudes can have the phases \(\mu(q)\psi(N)\), making all their terms add. For example take \(F_\psi=z^{-1/2}\mu(q)\psi(N)\) on \(|u|\le c\) for these conductors, zero elsewhere in this test. The inverse phases cancel, and the real part of \(e^{-iu}(1-iu)^{-3/2}\) stays positive for sufficiently small fixed \(c\). This common interval lies inside every such cell. No selected conductor induces a character at another multiple up to \(Q\). The resulting mixed coefficient is \(\gg\sqrt N Q\). These are test amplitudes for character orthogonality, not Dirichlet zeros. [U] For the genuine mixed coefficient at square-root order one needs cancellation within (7), over denominators, or with the boundary modes. ERH does not provide this via the individual field bound.

[P] There is an alternative that controls **both** \(q\mid N\) and \(q\nmid N\) for the genuine fields. Using the \(1+|u|\) branch of (8), also valid for all zeros, gives on any subset
\[
 \int_{\text{cells of }q}|MZ|\,d\alpha
    \ll \sqrt N L\,\min(U_q,\sqrt{U_q}).
\]
At the balanced order summation gives \(O(N L)\). At \(Q>\sqrt{2\pi N}\) split at \(q=2\pi N/Q\). Summing \(q^{-1/2}\) below and \(q^{-1}\) above gives
\[
 \int_{\mathbb T}|MZ|\,d\alpha \ll {N^{3/2}\over Q}L^2 .
                                                               \tag{9}
\]
Thus \(Q=\lfloor N^{2/3}\rfloor\) gives \(O(N^{5/6}L^2)\). This choice balances the mixed-term power \(3/2-\theta\) with the crude residue-interaction power \((1+\theta)/2\). Formula (9) holds for \(Z_{<Y}\), the full field, and each restricted field separately. This improvement changes the pieces \(M,Z,R\). Wave 3 transfers the resulting estimate for their *combined signed coefficient* back to the original dissection.

## 4. The effective heights and the obstruction to a norm proof

[P] At square-root order put \(q\asymp D\), \(U\asymp Q/D\) and \(L_T=\log(2QT)\). For a dyadic height \(T\ge2\) a more detailed version of the shell bound is
\[
 E_{D,T}\ll D^2 T L_T^2
       (1+\log^+(U/T))e^{-cT/U}.                             \tag{10}
\]
For \(|\gamma|<2\) use \(T=1\). This follows by summing the shell squares, whose exponential is \(e^{-cT/V}\), over dyadic \(1\le V\ll U\), including the central interval. The constants in \(U\) and the exponential can be enlarged. A block can carry order \(N\) in this estimate only if its right side allows that size. Exponential suppression is continuous, so there is no literal compact support.

[P] Several thresholds have different meanings.

- [P] Summing in \(q\), the field above height \(t\ge2\) has squared norm \(O(N\log^2(2Qt)/t)\) by Wave 3. Thus for polylogarithmic \(t\gg L^2\) with \(t/L^2\to\infty\) it has energy \(o(N)\). To remove it **including interactions** with \(S\) by Cauchy, \(t/L^3\to\infty\) suffices. At the other end (3) gives \(o(N)\) on \(q=o(Q/L^2)\), and \(o(N/L)\) on \(q=o(Q/L^3)\), interpreted as cumulative cutoffs.
- [P] For \(q\asymp Q\), \(U=O(1)\). Here \(|\gamma|>A\log L\) has energy \(o(N/L)\) when \(A\) is sufficiently large, by (10) and dyadic Minkowski. More generally one can excise \(|\gamma|>A(1+U_q)\log L\) at that cost: retain half the exponential on every shell in the proof of (3), obtaining an arbitrary inverse power of \(L\) in the squared bound. No fixed absolute cutoff gives that conclusion from (10). Fixed-height gamma attenuation is a fixed factor while the zero-count bound grows with the conductor.
- [P] For fixed \(t=O(1)\) the square-root dissection permits \(O(N L^2)\) for the energy below \(t\), by direct summation of (10). Neither this upper bound nor a microscopic repulsion law proves a lower bound for the particular sharp band \(|\gamma|<1\). For \(1<t<L^4\) use (10) locally and the \(N L^2/t\) bound for the cumulative upper tail. In particular, already at \(t=K L\) for a sufficiently large constant \(K\), the field below \(t\) **must** have energy \(\gg NL\), by (11) and the triangle inequality.

[P] The last lower bound follows from the primes themselves. On \(B\), Wave 3 derives \(\|1_B S\|_2^2\ge(15/32-o(1))NL\) by evaluating the H2 major-arc energy. At square-root order \(\|M\|_2^2\le(1/4+o(1))NL\). The residue is \(o(\sqrt{NL})\) in norm and the Wave 3 high tail at \(Y=L^4\) is \(O(\sqrt N/L)\). Hence
\[
 \|1_B Z_{<Y}\|_2
 \ \ge\big(\sqrt{15/32}-1/2-o(1)\big)\sqrt{NL}.              \tag{11}
\]
In particular the genuine field exceeds the squared energy \(N\) by a growing factor. The same argument with the all-ordinate field gives the claim for \(t=KL\) since the tail norm there is \(O(\sqrt{NL/K})\).

[I] The Katz–Sarnak microscopic scale is \(1/\log d\) in ordinate, whereas a fixed interval in ordinate contains a growing number of microscopic spacings. An upper count of \(O(1)\) in a microscopic window implies no lower bound in that window, and supplies no joint target phase. Equation (11) holds for actual fields under ERH even if one adds a compatible repulsion hypothesis and excludes exceptional central zeros. A uniform \(O(1)\) count in *every* unit interval across the whole low band would be a much stronger assumption: replacing both zero-count factors by constants in the bounded-height and dyadic shell estimates would give \(O(N)\) for the entire low field, contradicting (11). One cannot remove the genuine low square by an \(o(N)\) unsigned bound. Hölder also gives \(\int_B|Z_{<Y}|^4\gg N^2L^2\).

[P] The square-root order is a transition, not a minimax theorem. For \(Q=N^\theta\) up to rounding, the squared shell budget before summing over \(V\ge1\) is
\[
 \ll \min\{Q^2,(N/(QV))^2\}\,T\log^2(2QT)e^{-cT/V}.
\]
For the central shell one may replace the count by \(O(\min(Q^2,N))\), using the actual length if \(U_q<1\). For \(\theta<1/2\) the transition height is \(T_*=N/Q^2\), where the budget has power \(Q^2T_*=N\). The norm of the entire field below \(L^4\) is \(o(\sqrt N)\) there, by bounding the number of shells by \(O(L)\), counting at most \(Q^2\) centers and summing the polylogarithmic norms. Yet \(\|1_B S\|_2^2\ge(15/32-o(1))NL\) and \(\|M\|_2^2\le(\theta/2+o(1))NL\). Thus the discarded high field genuinely has norm \(\gg_\theta\sqrt{NL}\). Wave 3's low-height reduction cannot be transferred by the same high-tail norm argument to these coarser cells. For \(\theta>1/2\), most cell length has \(U_q\ll1\); (9) saves a power, and the next section makes the remaining height and window dependence explicit.

## 5. A target-specific zero statistic with no beta integration

[P] Take
\[
 Q=\lfloor N^{2/3}\rfloor,\quad D=Q/L^4,\quad K=L^2,\quad T_0=2\log L,
 \qquad b_\psi=\sum_{|\gamma_\psi|<T_0}\Gamma(1/2+i\gamma_\psi)N^{i\gamma_\psi}.
\]
For each \(q\) retain the characters of inducing conductor \(d\ge q/K\). Define the dimensionless real number
\[
 \mathcal P_N=\Re\!\!
 \sum_{\substack{D<q\le Q\\q\nmid N}}\ \sum_{a\bmod q}^{*}
 \ell_{q,a}\,e(-Na/q)
 \left(\sum_{\substack{\chi\bmod q\\ {\rm cond}(\chi)\ge q/K}}
               c_\chi\chi(a)b_{\chi^*}\right)^2.            \tag{12}
\]
All these cells are in \(B\). In particular the omission \(q\mid N\) does not omit partially shared factors. The square in (12) is an ordinary complex square. With \(F_N(B)=\Re\int_B S^2e(-N\alpha)d\alpha\), the result is
\[
 F_N(B)=N\mathcal P_N+O(N/\sqrt L),\qquad
 I_{\rm low}^{\,Q=\lfloor\sqrt{2\pi N}\rfloor}(N)
                 =N\mathcal P_N+O(N/\sqrt L).               \tag{13}
\]

1. [P] Apply (2), (5) at the enlarged order, and (9) to the **all-ordinate** field. This gives \(F_N(B)=\Re\int_B Z^2e(-N\alpha)d\alpha+O_\epsilon(N^{1+\epsilon}/H+\sqrt{NQ}L^3+QL^4+N^{3/2}L^2/Q)\). All these errors save a power of \(N\) for sufficiently small \(\epsilon\). Equation (3) discards \(q\le D\) at a cost \(O(N/L^2)\) in this square integral, and all \(q\mid N\) at \(O((N/Q)\tau(N)L^2)\). The sets of cells are disjoint.
2. [P] On the remaining cells \(|u|\le\eta=2\pi N/(DQ)\ll N^{-1/3}L^4\). At \(|u|\le\eta\), differentiating \(\Gamma(\rho)N^{i\gamma}(1-iu)^{-\rho}\) in \(u\) costs \(O((1+|\gamma|)e^{-c|\gamma|})\) for large \(N\). Its sum per primitive character is \(O(L)\). By (2) and orthogonality on a common interval, replacing the all-ordinate field by its cell-center value has squared norm cost \(\ll N\eta^2L^2\sum_{q\le Q}\varphi(q)/(qQ)\ll N\eta^2L^2\). Here and below “squared norm cost” means the squared norm of the difference of the two fields. The all-ordinate field has norm \(O(\sqrt{NL})\) by (2) and the bounds for \(S,M,R\). Cauchy controls the difference of the two squares. Replacing \(e(-N\beta)\) by 1 then costs \(O(\eta NL)\) in the integral.
3. [P] At the center, \(|\Gamma(1/2+i\gamma)|=(\pi/\cosh(\pi\gamma))^{1/2}\). The discarded sum of absolute gamma weights per character above \(T_0\) is \(O(\log(2q(2+T_0))e^{-\pi T_0/2})\) by unit-interval counting. Using \(\ell_{q,a}\le2/(qQ)\) and (2), the change in field norm is \(O(\sqrt N L e^{-\pi T_0/2})\). Its interaction costs \(O(N L^{3/2-\pi})\), smaller than \(N/\sqrt L\). This is why a multiple of \(\log\log N\) suffices here.
4. [P] To discard small inducing conductors, write \(q=dr\). The imprimitive Gauss coefficient vanishes unless \(r\) is squarefree and \((d,r)=1\), in which case \(|\tau_q(\bar\chi)|^2=d\). This follows by inclusion–exclusion on the unit condition in the additive Gauss sum of frequency one. The total squared coefficient weight to be deleted, including the center count and maximum length up to an absolute factor, satisfies
\[
 \sum_{q\le Q}{\varphi(q)\over qQ}
       \sum_{\chi:\,q/{\rm cond}(\chi)>K}|c_\chi|^2
 \le {1\over Q}\sum_{r>K}{1\over r\varphi(r)}
                      \sum_{d\le Q/r}{\varphi^*(d)\over\varphi(d)}
 \le\sum_{r>K}{1\over r^2\varphi(r)}\ll K^{-2}.
\]
For the last bound the mean of \(r/\varphi(r)\) is bounded by expanding it as \(\sum_{h\mid r}\mu^2(h)/\varphi(h)\). Since \(|b_\psi|\ll L\), the change in field norm is \(O(\sqrt N L/K)\). Its interaction with the retained field costs \(O(N L^{3/2}/K)=O(N/\sqrt L)\). This proves the first identity in (13). The second follows from Wave 3 (5) for the same set \(B\). In particular, it holds for any of Wave 3's admissible choices of the *original* cells.

[P] The field in (12) itself still has energy \(\gg NL\) when multiplied by \(\sqrt N\) and extended constantly on the retained cells. Indeed at this order \(\|M\|_2^2\le(1/3+o(1))NL\). Subtract \(M,R\) from \(1_BS\), then apply the field norm errors in steps 1–4. The resulting lower constant in norm is at least \(\sqrt{15/32}-1/\sqrt3-o(1)>0\). Thus the norm obstruction survives simultaneously restricting the conductors, the heights and the denominators in (12).

### What the signed center sum does

[P] Expanding (12) gives the exact kernel
\[
 \sum_a^*\ell_{q,a}(\chi\chi')(a)e(-Na/q)
\]
multiplying \(c_\chi c_{\chi'}b_{\chi^*}b_{\chi'^*}\). On a common interval of length \(\ell\) this would be \(\ell G_q(\chi\chi';-N)\). At the original square-root order the exact kernel at each \(\beta\) uses the indicator of the actual cell and the two factors \(F_{\chi^*,<Y}(\beta)F_{\chi'^*,<Y}(\beta)\) before integration. Formula (1) gives the endpoint masks explicitly. A complete center sum is a Gauss sum for the product character. A Kloosterman phase enters when completing an inverse-dependent mask.

[P] For any \(q\), if \(\chi\chi'\) is induced by the primitive \(\psi\bmod f\), inclusion–exclusion gives the exact complete formula
\[
 G_q(\chi\chi';n)=\tau_f(\psi)
  \sum_{\substack{h\mid q/f,\ (h,f)=1\\ k=q/(hf),\ k\mid n}}
       \mu(h)\psi(h)\, k\,\bar\psi(n/k).
\]
When \(q\mid N\) it is \(\varphi(q)\) for \(\chi'=\bar\chi\) and zero otherwise, directly by orthogonality. For exact central zeros on a common interval this leaves, before beta integration,
\(\pi z^{-1}\varphi(q)\sum_\chi \chi(-1)|c_\chi|^2 m_{\chi^*}^2\), where \(m_{\chi^*}\) is the central multiplicity. Indeed \(m_{\bar\psi}=m_\psi\) and \(c_\chi c_{\bar\chi}=\chi(-1)|c_\chi|^2\). Even here parity enters the sign. For nonzero small ordinates each pair also has the phase \(N^{i(\gamma+\gamma')}\); ordinates of size \(1/L\) already change this phase by order one.

[P] For prime \(q\nmid N\), every nonprincipal product character gives a Gauss entry of magnitude \(\sqrt q\) and a principal product gives \(-1\). Nevertheless the complete matrix \(G_q(\chi\chi';-N)/\varphi(q)\) has **every singular value equal to one**, for any \(q,N\). It is \(U^{\mathsf T}\operatorname{diag}(e(-Na/q))U\) with \(U_{a\chi}=\chi(a)/\sqrt{\varphi(q)}\) unitary. With the actual \(\ell_{q,a}\) inserted its singular values are precisely the \(\ell_{q,a}\). Both assertions follow by unitary multiplication. The full matrix norm therefore gives no saving from the small individual entries. [U] A lower bound on its quadratic form for the specific arithmetic vectors \(c_\chi b_{\chi^*}\), after the \(q\)-sum, remains missing. It could exploit cancellation within or across moduli.

### Center cancellation does remove sparse families of pairs

[P] There is a further saving from the *individual* center sums, even though the full matrix has norm one after normalization. In the expansion of (12) one may also discard all of the following, together costing \(O(N/\sqrt L)\) in (13):

- [P] First discard the entire cells whose denominator has powerful part \(h(q)=\prod_{p^j\parallel q,\ j\ge2}p^j>L^8\).
- [P] On the remaining cells discard the terms with \(\chi'=\chi\), and all terms for which the product character \(\chi\chi'\) has conductor \(f\le Q^{1/2-\delta}\), for any fixed \(0<\delta<1/2\). In particular every conjugate-character pairing drops out. Retain the original coefficient of every surviving term.

[P] For the first deletion, center orthogonality and the length majorant give \(O(NL^2/Q)\) per denominator for the integral of the squared modulus of the retained field. There are \(O(Q L^{-4})\) excluded denominators, since \(\sum_{h>x,\ h\ {\rm powerful}}h^{-1}\ll x^{-1/2}\). Indeed each powerful integer is of the form \(a^2b^3\) with \(b\) squarefree, so its counting function is \(O(\sqrt x)\). This deletion costs \(O(N/L^2)\).

[P] For the second deletion write \(q=hs\) with \(s\) squarefree and \((h,s)=1\). For any product character \(\xi\) the actual weight \(\ell_{q,a}\), as a function of \(a^{-1}\bmod q\) by (1), has supremum and total cyclic variation \(O(1/(qQ))\). Fourier completion by summation by parts therefore has coefficient absolute sum \(O(\log(2q)/(qQ))\). On the factor \(h\), bound the completed hybrid sum trivially by \(h\). On each prime \(p\mid s\), use the classical finite-field Weil bound
\[
 \left|\sum_{x\bmod p}^*\xi_p(x)e((Ax+B/x)/p)\right|
    \le 2\sqrt p\quad\text{if }(A,B)\not\equiv(0,0)\pmod p .
\]
For one nonzero coefficient this is the elementary Gauss bound; when both vanish the trivial bound is \(p\). The CRT twists of \(A=-N\) and inverse frequency \(B\) are by units. Multiplication gives \(2^{\omega(s)}\sqrt{s(s,N)}\,h\) per completed sum. Consequently on \(h\le L^8\), uniformly in the product character,
\[
 \left|\sum_a^*\ell_{q,a}\xi(a)e(-Na/q)\right|
        \ll_\epsilon {N^\epsilon\sqrt{q(q,N)}\over qQ}.
\]
For one prescribed \(\xi\), Cauchy and \(\sum|c_\chi|^2=1\) bound the sum of \(|c_\chi c_{\xi\bar\chi}b_{\chi^*}b_{(\xi\bar\chi)^*}|\) by \(O(L^2)\). The diagonal \(\chi'=\chi\) has the same total absolute coefficient weight, independently of its product characters. The number of possible products of conductor at most \(F\) is at most \(\sum_{f\mid q,\ f\le F}\varphi^*(f)\le F\tau(q)\). Using \(\sum_{q\le Q}\sqrt{(q,N)/q}\ll\sqrt Q\tau(N)\), the deleted pairs in the dimensionless statistic cost \(O_\epsilon((1+F)N^\epsilon/\sqrt Q)\). Taking \(F=Q^{1/2-\delta}\) saves a power of \(N\). This proof works for any subset of the indicated pair entries on the retained cells.

[P] Denote the statistic with both deletions by \(\mathcal P_N^\circ\). One may replace \(\mathcal P_N\) by \(\mathcal P_N^\circ\) in (13) and (14). Thus the fixed-target hypothesis need only concern **distinct input characters with large product conductor**, in addition to the height and individual conductor restrictions of (12). The energy floor applies to the underlying field; after removing entries its quadratic form need not be the square of a new field.

## 6. Exactly what a one-sided hypothesis buys

[P] The H2 major-arc evaluation gives \(F_N(A_y)=NJ(T_y)D_H(N)+o(N/\sqrt L)\): its explicit normalized error is \(d_y\ll N^{-7/32}L^{O(1)}\) with fixed \(C\) (the stated H2 formula gives at least this saving). By (4) and the \(O(T_y^{-2})\) integral tail this is \(N\mathfrak S(N)/e+o(N/\sqrt L)\). The proper-prime-power allowance is \(O(\sqrt N L)\). Thus for the ordered, exponentially weighted prime–prime coefficient \(P_N\),
\[
 {P_N\over N}={\mathfrak S(N)\over e}+\mathcal P_N+O(L^{-1/2}).
                                                               \tag{14}
\]
This also explains the precision of conditions expressed solely in terms of the new statistic.

- [P] Under ERH, \(\mathcal P_N=o(1)\) is equivalent to \(I_{\rm low}(N)=o(N)\) for H2, by (13). It gives the binary Hardy–Littlewood main term up to \(o(N)\) in this normalization.
- [P] The weaker one-sided condition \(\liminf_{2\mid N\to\infty}\mathcal P_N>-1/3\) implies \(I_{\rm low}(N)\ge-N/3\) eventually and hence Goldbach for every sufficiently large even \(N\). Even equality at the liminf suffices for eventual Goldbach: the major coefficient has a fixed margin, since \(\mathfrak S(N)\ge 2\prod_{p>2}(1-(p-1)^{-2})>1.32032\). [Singular series lower bound](../../proof/binary_goldbach_exceptional_proof.md)
- [P] A target-dependent sufficient hypothesis allows a vanishing margin:
\[
 \sqrt L\big(\mathcal P_N+\mathfrak S(N)/e\big)
             \longrightarrow+\infty\qquad(2\mid N\to\infty).
\]
Equation (14) then makes \(P_N>0\). At the level of fixed positive normalized margins, \(\liminf(\mathcal P_N+\mathfrak S(N)/e)>0\) is *equivalent* to \(\liminf P_N/N>0\). These implications use no finite verification. To cover all smaller even integers one would need a quantified onset and a matching finite proof.

[I] Formula (12) involves only zero ordinates, explicit gamma weights, finite character coefficients and exact rational cell lengths. It specifies which joint statistic would suffice. No universally weakest independent hypothesis for existence follows from this equivalence. [U] There is no bound here for the required negative part of (12), and hence no proof of pointwise Strong Goldbach under ERH.

[Q] A finite arithmetic cross-check covered all 120 products in (6) for \(q=15\), primitive conductors \(1,3,5,15\) with one character each, and \(0\le N<30\). The maximum discrepancy was below \(2\cdot10^{-12}\) using complex floating point. Exact rational summation of (1) covered the entire circle at orders 9, 16 and 31. These checks test normalizations only.

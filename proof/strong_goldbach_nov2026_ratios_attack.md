# Binary Goldbach from Dirichlet ratios under ERH and Grand RH

**Result.** The tested estimates do not prove binary Goldbach. At denominator distance $\eta$ from the critical line, a direct Dirichlet-character calculation gives a normalized critical-numerator ratios error $O_{\eta,\epsilon}(q^{-\eta+\epsilon})$ for small fixed $\eta$. It uses a joint cutoff on the product of the Möbius indices. Two separate cutoffs give exponent $\eta/(2(1-\eta))$. Applied directly to the parity-weighted logarithmic derivatives, GRH and a cutoff at $mn\asymp q^2$ reach $O(q^{1-2\eta+\epsilon})$ for the integrated absolute error. This reaches the critical exponent; GWX need a saving exceeding $2\eta$ for their fixed-line asymptotic. Even granting a fixed-conductor mollified moment to length $q^{0.532}$ would only certify a reciprocal substitution saving of $0.532\eta$ by the individual GRH tail estimate. The exponent $0.532$ in the supplied Pascadi result concerns the height aspect of zeta. An optimal conductor-aspect length, or a necessary length for the true averaged ratio, cannot be inferred from it.

There is a weaker sufficient input. A single real, parity-weighted integral per target may lose any fixed fraction strictly below one of the projected main term. Alternatively, on lines at distance $c/\log(2q)$ a conductor-local $o(\varphi^*(q))$ estimate in an explicit weighted norm suffices for the asymptotic. Both statements are derived below. The last section gives an exact positivity test reaching the endpoint of the finite verification. An asymptotic with unspecified constants proves existence for sufficiently large even integers and needs a finite bridge to give the assertion for every even integer.

## 1. Which ratios and which theorem?

The local GWX PDF, Hypothesis 1.1, uses **conjugate characters** in the second numerator and denominator. A bar on the character does not conjugate the shift. In this report
\[
 R_q(a,b;s,t)=\sum_{\chi\bmod q}^*
 \frac{L(a,\chi)L(b,\bar\chi)}{L(s,\chi)L(t,\bar\chi)} .
\]
The bars matter already for orthogonality. The primitive sum is unnormalized. GWX take $0<\omega_D\le1/2$ independent of every sufficiently small fixed $\eta>0$, numerator real parts $1/2$, denominator real parts $1/2+\eta$, and heights at most $100\log(2q)$. They require both terms of their $M_q$, at every conductor $q>1$, with error $O_{\eta,\epsilon}(q^{1-\omega_D+\epsilon}(1+T)^B)$. Theorem 1.1 then gives $G(N)=N\mathfrak S(N)+O_\epsilon(N^{1-\omega_D+\epsilon})$ for even $N$, where $G(N)=\sum_{m+n=N}\Lambda(m)\Lambda(n)$. The positive lower bound $\mathfrak S(N)\ge 2\prod_{p>2}(1-(p-1)^{-2})>0$ is uniform.

To obtain the mixed derivative one needs numerator disks about $(s,t)$ and the reflected arguments $(1-t,1-s)$. On disks of radius $r<\eta/4$, GWX (3.26) certify the exponent $\omega=\omega_D-8(\eta+r)(2+\omega_D)$. Their choice makes $\omega>2\eta$. At a *fixed* choice the error in $G(N)$ is $O(N^{1-\omega+2\eta+\epsilon})$. Taking $\eta$ small in terms of the final $\epsilon$ gives their stated exponent. A saving merely positive for each fixed $\eta$, with no comparison to $2\eta$, does not justify this argument.

Appendix A, opening paragraph on p. 39, explicitly retains a positive power saving for the character argument. Its moving-line hypotheses 2.4 and 2.5 concern the zeta and angular Hecke families. Section 3.4's qualitative Goldbach asymptotic uses the power saving from §3.3. The moving-line Dirichlet criterion in §5 below is a separate deduction.

## 2. What a reciprocal truncation actually costs

Write $s=1/2+\eta+it$ and $Q=q(2+|t|)$. For a fixed smooth $V$ supported on $[0,2]$ and equal to one on $[0,1]$, use
\[
 P_M(s,\chi)=\sum_n \mu(n)\chi(n)n^{-s}V(n/M).
\]
The Mellin transform of $V$ has residue one at zero and rapid vertical decay on fixed strips away from the pole (integrate its compactly supported derivative). Shift its inversion integral for $P_M$ from $\Re u=1$ to $-\eta+d$ with $0<d<\eta$. Dirichlet GRH gives $1/L(1/2+d+iy,\chi)\ll_{d,\epsilon}(q(2+|y|))^\epsilon$. Thus
\[
 P_M(s,\chi)-1/L(s,\chi)\ll_{d,\eta,\epsilon} Q^\epsilon M^{-\eta+d}. \tag{1}
\]
For $M=q^\theta$ with fixed $\theta>0$, $|t|\ll\log q$, this is $O_{\eta,\theta,\epsilon}(q^{-\theta\eta+\epsilon})$ by choosing $d$ sufficiently small. A sharp cutoff at $M$ gives the same fixed-power exponent by partial summation from the GRH twisted Mertens bound $\sum_{n\le x}\mu(n)\chi(n)n^{-it}\ll_\epsilon x^{1/2+\epsilon}(q(2+|t|))^\epsilon$. One can obtain the latter by truncated Perron at a half-integer, height a sufficiently large power of $xQ$, shifting to $1/2+\epsilon/2$ and using the reciprocal bound there with a smaller epsilon. Smoothing suffices here.

On the critical numerator lines GRH gives Lindelöf bounds for both factors. The identity $xy-uv=(x-u)y+u(y-v)$ and (1) now bound the replacement error for $R_q/q$ by $O(q^{-\theta\eta+\epsilon})$. The second reciprocal does **not** double this exponent. For the power-saving test, (1) certifies $q^{-\delta+\epsilon}$ at $\theta\eta\ge\delta$. The resulting budgets are

| Target for this absolute-error argument | Length budget |
|---|---|
| $o(1)$ for fixed $\eta$ | Every fixed $M=q^\theta$, $\theta>0$, suffices for substitution alone. |
| A prescribed saving $\omega_D$ | $\theta\ge\omega_D/\eta$. No fixed $\theta$ covers arbitrarily small fixed $\eta$. |
| A saving exceeding $2\eta$ | $\theta>2$, even before allowing an interpolation loss. |
| Moving $\eta=c/\log q$ | The formal factor $M^{-\eta}$ equals $e^{-c\theta}$ at fixed $\theta$. Even this factor tends to zero only if $\log M/\log q\to\infty$. To make it $q^{-\delta}$ takes $\log M=(\delta/c)(\log q)^2$. |

The last row is an algebraic diagnostic. The constants in (1) are for fixed $d,\eta$ and $q^\epsilon$ cannot be discarded in a logarithmic-limit argument. None of these budgets is a lower bound on the length of a successful mean-value approximation. A cancellation in the discarded terms can change the answer.

**A uniform moving-line upper bound.** For $D=c/(2\log q)$ and large $q$ one has
\[
     |1/L(1/2+D+iy,\chi)|\ll_c [q(3+|y|)]^{C_c}. \tag{1a}
\]
Here is a justification of the dependence on $D$. Set $Q_y=q(3+|y|)$ and $U=\max(1,\tfrac14\log\log Q_y)$. Under GRH the number of zeros with $|\gamma-y|\le 1/U$ is $O(\log Q_y/U)$. Indeed apply the Dirichlet explicit formula to the translated test $h(u)=(\sin(U(u-y))/(U(u-y)))^2$. It is nonnegative on real ordinates and bounded below by an absolute positive constant in that interval. Its Fourier transform in angular frequency is supported on $[-2U,2U]$ and bounded by $O(1/U)$. The conductor and gamma terms are $O(\log Q_y/U)$ by integrating $h$ against $O(\log(q(3+|u|)))$. The prime terms are $O(U^{-1}\sum_{n\le e^{2U}}\Lambda(n)/\sqrt n)=O(e^U/U)$ by Chebyshev and partial summation. There is no pole term for a primitive nonprincipal character. This proves the count, also with centers within two units of $y$ using the same $U$.

Integrate the standard local expansion of $L'/L$ horizontally from $2+iy$ to $1/2+D+iy$. Zeros within $1/U$ cost $O((\log Q_y/U)\log(2/D))=O_c(\log Q_y)$, even with multiplicities, since $Q_y\ge q$. In the remaining dyadic shells $r<|\gamma-y|\le 2r\le 2$ with $r\ge 1/U$ the count is $O(r\log Q_y)$ by covering. Each integrated reciprocal costs $O(\log(3/r))$, and the sum of $r\log(3/r)$ over these shells is bounded. The regular remainder costs $O(\log Q_y)$. Exponentiating gives (1a), also at distances between $D$ and $1/4$.

Use exponential smoothing $e^{-n/M}$ at $\eta=2D$. On shifting the Mellin integral with $\Gamma(u)$ to $\Re u=-D$, (1a) bounds the error by $M^{-D}q^{O_c(1)}$ for $|t|\ll\log q$. The gamma integral near zero costs $O(\log(2/D))$, and its exponential tail absorbs the fixed polynomial height growth. Hence $\log M=K(\log q)^2$ with $K$ sufficiently large in terms of $c$ and the desired power certifies any prescribed fixed power accuracy, also after multiplying by the second reciprocal and the critical numerator bounds. Cutting this smoothed sum at $M(\log q)^3$ has negligible absolute error by exponential decay. This gives a rigorous sufficient length on the scale of the power-accuracy diagnostic in the table. It does not establish a lower bound for the true ratios error.

**A finite-block check.** For prime $p$, $1\ll M<p/2$, the mean square over all characters of the *single* omitted block $M<n\le2M$ of the raw reciprocal series is exactly $\sum_{M<n\le2M}\mu^2(n)n^{-1-2\eta}\asymp M^{-2\eta}$, by orthogonality and the positive density of squarefrees. The comparison is uniform for $0\le\eta\le1/4$. Removing the principal character costs $O(M^{1-2\eta}/p)$ in the normalization by $p-1$. At $M=p^\theta$, $0<\theta<1$, this block has RMS of order $M^{-\eta}$, of constant order for the moving line. Blocks further out can correlate with it modulo $p$. This calculation tests the size of a block; it does not lower-bound the entire tail or its contribution to $R_p$.

## 3. A fixed-conductor mollified moment that can be estimated

Here is a length calculation for the actual family. Normalize errors by $q$, use the critical numerator lines and the logarithmic heights of Hypothesis 1.1, and fix $0<\eta<1/8$. Take $M=q^\theta$ with fixed $\theta>0$ and the smooth cutoff of (1). Let $R_{q,M}$ denote the sum with both reciprocals replaced by $P_M$. Let $D_{q,M}$ be the **integer diagonal** in both pieces of the approximate functional equation for $R_{q,M}$, with the parity counts and archimedean weights retained. Then
\[
 \frac{R_{q,M}-D_{q,M}}q
 \ll_{\eta,\theta,\epsilon} q^{-1/2+\epsilon}M^{1-2\eta}. \tag{2}
\]
Thus an asymptotic expansion with additive error $o(q)$ around the finite diagonal is available for **each** polynomial of length $q^\theta$ when $\theta<1/[2(1-2\eta)]$. A relative asymptotic is not intended at shifts where the model can be small. This endpoint is the strict range of the bound (2), not an optimal length theorem.

**Proof of (2).** Use the two-piece approximate functional equation for $L(a,\chi)L(b,\bar\chi)$ with even Mellin auxiliary function $e^{u^2}$. It follows by integrating the completed product shifted by $u$ against $e^{u^2}/u$ and reflecting the contour. The two root numbers cancel. Both pieces have positive indices $m,n$, weight of magnitude $(mn)^{-1/2}$ before smoothing, and smooth cutoff at $mn\le q^{1+\epsilon'}$ up to arbitrary inverse powers of $q$, for any fixed $\epsilon'>0$. The dual prefactor has modulus one. The gamma factors depend on parity and shifts. On each displaced vertical line their ratios grow polynomially in $1+T$ times a polynomial-exponential in $|\Im u|$ absorbed by $e^{u^2}$, by Stirling. This proves the truncation by a far-right shift and bounds the retained smooth weights by $O(q^{\epsilon'})$ by a near-zero positive shift. The discarded contribution stays negligible after either polynomial of fixed power length is inserted, by taking the far-right shift large enough.

With mollifier indices $r,v\le 2M$, set $x=mr$, $y=nv$ after labeling the dual indices by their characters. Only units modulo $q$ contribute. For fixed parity $e$ the projector is half the sum of the primitive orthogonality kernels for $x\equiv y$ and $x\equiv-y$, with multiplier $(-1)^e$ on the latter. Each kernel is $\sum_{d\mid q,\ d\mid x\mp y}\mu(q/d)\varphi(d)$. Keep $x=y$ with its exact coefficient $M_e(q)$, the number of primitive characters of parity $e$.

On a dyadic box $m\asymp m_0$, $n\asymp n_0$, $r\asymp R$, $v\asymp V_0$, let $U=m_0R$, $V=n_0V_0$. If the off-diagonal congruence has a solution then $d\ll\max(U,V)$, since the relevant nonzero integer is $x-y$ or $x+y$. For each choice of the smaller variable there are $O(\max(U,V)/d+1)$ choices of the other, hence $O(UV/d)$ pairs. Lifting to factorizations costs $q^{\epsilon'}$ by the divisor bound at fixed $\theta$. The coefficient magnitude per lift is $\ll q^{\epsilon'}(UV)^{-1/2}(R V_0)^{-\eta}$. Summing $\varphi(d)/d\le1$ over $d\mid q$ costs $q^{\epsilon'}$. The normalized box bound is therefore
\[
 q^{-1+O(\epsilon')}\sqrt{m_0n_0}\,(R V_0)^{1/2-\eta}
 \ll q^{-1/2+O(\epsilon')} M^{1-2\eta}.
\]
The dyadic counts and arbitrarily small losses fit in $q^\epsilon$. This argument includes both signs and composite conductors.

**Identification of the full diagonal.** Uniformly on the same window,
\[
 (D_{q,M}-M_q)/q\ll_{\eta,\theta,\epsilon}
 q^\epsilon M^{-\eta+\epsilon}+q^{-h+\epsilon},
 \qquad 0<h<\eta \text{ fixed}. \tag{3}
\]
Here and below constants can depend on $h$. To check the extension of the diagonal, write $r=g r'$, $v=g v'$, $(r',v')=1$. The equation $mr=nv$ gives $m=v'\ell$, $n=r'\ell$. The absolute coefficient is bounded by $g^{-1-2\eta}(r'v')^{-1-\eta}/\ell$. The smooth numerator weights cost at most $q^\epsilon$ in the $\ell$-sum, uniformly in $r',v'$, by bounding the weight on a small positive Mellin line by $O(q^\epsilon(mn)^{-b})$ for sufficiently small $b>0$. Where the cutoffs differ from one, $g\max(r',v')>M$. Rankin's inequality with power $\eta-\epsilon'$ bounds this tail by $O(q^\epsilon M^{-\eta+\epsilon'})$. It applies to both approximate-functional-equation pieces.

For completeness, the direct infinite diagonal of parity $e$, per character, is the integral on a positive line of
\[
 g_e(u;a,b)\,Z_q(a+u,b+u;s,t)\,\frac{e^{u^2}}{u}\frac{du}{2\pi i},
\quad
 g_e(u;a,b)=(q/\pi)^u
 \prod_{j\in\{a,b\}}\frac{\Gamma((j+u+e)/2)}{\Gamma((j+e)/2)} ,
\]
where the product takes the two arguments with multiplicity. The Euler factors follow by taking the constant character-power coefficient at each prime, as in GWX (2.1)–(2.2). The dual integral is the same expression at $a'=1-b$, $b'=1-a$, multiplied by $X_{q,e}(a)X_{q,e}(b)$ as defined in GWX §3. Shifting both integrals to $-h$ gives the two $u=0$ residues in $M_q$. The poles at $u_0=(1-a-b)/2$ and $-u_0$ from the two numerator zeta factors cancel in the sum: the shifted argument pairs agree there in the same order, the completed gamma factors agree with the dual prefactor included, and $e^{u^2}/u$ takes opposite values. Interpret $u_0=0$ by continuity from distinct poles. On the new line the denominator zeta factors have real part $1+\eta-h>1$, the arithmetic products converge absolutely (the local remainder is of quadratic order in terms $p^{-1+O(h)}$), and the finite Euler factors cost $q^\epsilon$. Stirling and standard zeta bounds leave $O(q^{-h+\epsilon})$ per character. This proves (3), including the reflected main term. The normalization $q$ in these estimates also covers conductors having no primitive characters.

Combining (1)–(3), the limiting exponents certified by the three errors are $\theta\eta$, $1/2-(1-2\eta)\theta$, and $h<\eta$. Balancing the first two at $\theta=1/[2(1-\eta)]$ gives the separate-cutoff exponent $\eta/[2(1-\eta)]$ with arbitrary $\epsilon$ loss, on choosing $h$ between this value and $\eta$. This gives a fixed-$\eta$ critical-line ratios estimate under Dirichlet GRH. It falls below $2\eta$ even if its exponent could pass to the differentiated parity formula without loss. Forcing $\theta>2$ instead makes (2) ineffective for small $\eta$.

**Joint truncation gives a stronger fixed-$\eta$ result.** Replace the two independent weights by $V(rv/Y)$ in the double Möbius sum. Mellin inversion now has the product $1/[L(s+u,\chi)L(t+u,\bar\chi)]$ on a single contour. Both factors satisfy the same fixed-distance GRH bound on $\Re u=-\eta+d$, so the normalized substitution error is $O(q^\epsilon Y^{-\eta+d})$ for fixed $d\in(0,\eta)$ and $Y$ of fixed polynomial growth. The proof of (2) works box by box with $R V_0\ll Y$ and gives normalized error $O(q^{-1/2+\epsilon}Y^{1/2-\eta})$. In (3) the discarded diagonal has $g^2r'v'>Y$. Rankin's inequality now inserts $(g^2r'v'/Y)^{\eta-d}$, leaving exponents $-1-2d$ on $g$ and $-1-d$ on $r',v'$; all three series converge. The shifted diagonal integral is unchanged. At $Y=q$ all three normalized errors are $O_{\eta,\epsilon}(q^{-\eta+\epsilon})$, choosing $d$ arbitrarily small and $h$ arbitrarily close to $\eta$ in terms of $\epsilon$. This proves the stronger ratios estimate in the opening paragraph. It gives neither two independent length-$q$ polynomials nor a saving independent of $\eta$. The exponent $\eta$ is the optimum of this joint substitution and off-diagonal budget: for $Y=q^\nu$ the two exponents are $\nu\eta$ and $1/2-\nu(1/2-\eta)$, equal at $\nu=1$. Passing even this stronger exponent to the detector without loss would still leave an exponent deficit $\eta$.

**Where Pascadi enters the attempted improvement.** For prime $q$, the congruence after orthogonality is $mr\equiv\pm nv\pmod q$, with $mn\lesssim q$ and two independent Möbius factors. For example, Poisson summation on a smooth $m$-block of length $H$ gives the progression kernel
\[
 \frac Hq\sum_{j\in\mathbb Z}\widehat f(jH/q)
 e\!\left(\frac{\pm jnv\bar r}{q}\right),
 \qquad e(x)=e^{2\pi i x},
\]
where $\bar r$ is an inverse modulo $q$. The zero frequency must be evaluated separately. Reciprocity at a unit $r$ changes $\bar r/q$ to $-\bar q/r+1/(qr)$ modulo one. The resulting frequency is the product $jnv$, its available range depends on $H,n,v$, and the numerator $q$ in the inverse is fixed. For instance $H,n\asymp q^{1/2}$, $r,v\asymp M$ allow $|j|\lesssim q^{1/2}$ and $|jnv|$ up to order $qM$. Smooth cutoffs permit tails here. This is not a direct instance of a small free frequency $A$ with two balanced, independently averaged inverse variables. For composite conductors there are also all the $d\mid q$ and unit restrictions. Other rearrangements are possible, but require their own matched ranges, coefficient norms and main terms. Individual Lindelöf estimates do not perform those sums.

The supplied Pascadi summary gives a saving for certain balanced Kloosterman-fraction sums and a **zeta height integral** with twisting polynomial of length $T^{0.532}$. No fixed-$q$, two-reciprocal Dirichlet-family moment with GWX shifts, both parities and composite conductors is stated in that input. The height integral has no primitive-character projector at a prescribed $q$. Even a hypothetical asymptotic here for each polynomial at $M=q^{0.532}$, with the correct diagonal, would still need control of the infinite reciprocals. At that length (1) gives exponent $0.532\eta$ versus the $2\eta$ detector cost. If a bound instead controls a *combined* length, it must first be translated to the allowed lengths of the two factors. There is no exact maximal $M$ for this problem established by the quoted spectral gain. Equations (1)–(3) give explicit reachable and sufficient ranges and the bottleneck of that particular proof.

The other supplied November results concern zero density away from the line (no off-line zeros under the assumptions here), a simple-zero proportion for zeta, mixed moments of different families, and smoothing one-character sums. As supplied none includes the signed two-character-factor error at one conductor below. Artin or automorphic GRH also controls zero locations for individual functions; one would still have to identify a suitable spectral expansion and estimate its weighted family sum to derive that error.

## 4. The signed observable that the detector uses

Let $D_\chi(s)=L'(s,\chi)/L(s,\chi)$, $z=s+t-1$, $M_e(q)$ count primitive characters of parity $e$, and $\Delta=M_0-M_1$. Define
\[
 A_q(s,t)=\sum_\chi^*\chi(-1)D_\chi(s)D_{\bar\chi}(t),\qquad
 H_q(s,t)=\Delta P_q(z)+
 \{M_0X_{q,0}(s)X_{q,0}(t)-M_1X_{q,1}(s)X_{q,1}(t)\}C_q(z),
 \quad E_q=A_q-H_q . \tag{4}
\]
Here $P_q,C_q$ are GWX (2.6)–(2.7) and
$X_{q,e}(s)=(q/\pi)^{1/2-s}\Gamma((1-s+e)/2)/\Gamma((s+e)/2)$.
Thus $H_q$ is completely explicit. The weight is
\[
 w(v)=e^{20(1-v)}\left(\frac{\sin\pi(v-1)}{\pi(v-1)}\right)^2,\quad
 K(s,t)=\frac{\Gamma(s)\Gamma(t)}{\Gamma(s+t)}\widetilde w(s+t),
 \quad \widetilde w(b)=\int_0^\infty w(v)v^{b-1}\,dv .
\]
$K$ is the double Mellin transform of $w(u+v)$. Put $s=1/2+\eta+ix$, $t=1/2+\eta+iy$, and define
\[
 I_q(N;\eta)=\Re\int_{\mathbb R^2}
     K(s,t)N^{i(x+y)}E_q(s,t)\,\frac{dx\,dy}{(2\pi)^2}. \tag{5}
\]
Conjugation of shifts and characters makes the full integral real. Taking real parts *before* the complex phase and kernel have acted would change the test.

**Detector identity under Dirichlet GRH alone.** For even $N$ and arbitrary $0<\eta_q<1/4$, possibly depending on $N$, one has
\[
 G(N)=N\mathfrak S(N)+
 \frac{N}{\varphi(N)}\sum_{1<q\mid N}N^{2\eta_q}I_q(N;\eta_q)
 +O_\epsilon(N^{1/2+\epsilon}). \tag{6}
\]
The error here is separate from the retained integrals. To see this, first work on one small **fixed** line $\eta_0$. Orthogonality on the units uses $\chi(-1)\chi(m)\bar\chi(n)$, and $w(k)=\mathbf1_{k=1}$ for positive integers $k$. In the proof of GWX (3.12), with $\lambda=\mu=0$, insert (4) as an identity and retain the signed $E_q$ integrals exactly. All other estimates in that proof are independent of a ratios conjecture.

* Nonunit pairs with nonzero weight are powers of the same prime dividing $N$. They cost $O(\log^3(2N))$ since each coordinate is below $N$. Dropping imprimitive Euler factors costs $O_{\eta_0,\epsilon'}(N^{1/2+\eta_0+\epsilon'})$: shift the line of the finite Euler factor to $\epsilon'/4$, and the other logarithmic derivative to $1/2+\eta_0$. Principal residues with a missing Euler factor have their $1/\varphi(N)$ normalization.
* The principal double residue is $N^2 K(1,1)/\varphi(N)$. The one-residue and remaining principal integrals cost $O_{\eta_0,\epsilon'}(N^{1/2+\eta_0+\epsilon'})$. The $\Delta$ parts of $H_q$ cost $O_{\eta_0,\epsilon'}(N^{2\eta_0+\epsilon'})$ in total, using $|\Delta|\le2$.
* GWX (3.11)–(3.13) reduce the remaining gamma factors to the one-dimensional transform of $F(v)=v w(v)$. The exact model projection $\varphi(N)^{-1}\sum_{q\mid N}\varphi^*(q)q^{-z}D_q(z)=\sum_{N\mid h}\mathfrak S(h)h^{-z}$ on $\Re z>1$ then gives $N\sum_{k\ge1}\mathfrak S(kN)F(k)=N\mathfrak S(N)$. In this step $D_q(z)$ is GWX's *model Dirichlet series* (2.4), distinct from $D_\chi$. Restoring and subtracting $q=1$ cancels the principal double residue, with leftover $O_{\epsilon'}(N^{1/4+\epsilon'})$.

Take $\eta_0,\epsilon'$ sufficiently small in terms of $\epsilon$. Finally, each $N^{1+2\eta}I_q(N;\eta)$ is invariant under shifting the two vertical contours in $1/2<\Re s,\Re t<3/4$. For fixed $q,N$ the logarithmic derivatives in (4) are holomorphic there under GRH, and $P_q,C_q$ are holomorphic for $0<\Re z<1/2$, by their explicit formulas. On each closed intervening strip all have polynomial height growth and $K$ has exponential decay in $|x|+|y|$ by GWX (3.21)–(3.22). Shift one variable at a time. This exact change of lines is made **after** bounding the other terms on the fixed contours. It requires no uniform moving-line constant for those earlier estimates. This proves (6).

A pointwise real inequality for the *untwisted* logarithmic derivatives does not give (5). In particular on $t=\bar s$ the unsigned sum measures the total of even and odd energies, and the signed sum measures their difference. Off that slice the product is generally complex. Even a bound on the real part of $E_q$ everywhere provides no direct pointwise inequality for the rotated real part in (5). To recover parity from untwisted **ratios**, GWX (3.3) uses two numerator choices, their functional equations and the factor $(h_0+h_1)/(h_0-h_1)=-\cos(\pi(a-b)/2)/\sin(\pi(a+b-1)/2)$. At $a=1/2+\eta+iT$, $b=1/2+\eta-iT$ its magnitude is $\cosh(\pi T)/\sin(\pi\eta)$. The beta factor in $K$ compensates the exponential, leaving polynomial window losses in (3.23). Disks of radius $r\asymp\eta$ used in two Cauchy derivatives cost $O(\eta^{-2})$; near $x+y=0$ the parity inverse also has an $O(1/\eta)$ factor. A bare uniform undifferentiated $o(q)$ on the critical numerator lines cannot simply be differentiated twice on moving disks and passed through this inversion. Postulating (5) or a weighted estimate on (4) avoids both steps.

## 5. One-sided, wider-line and conductor-local criteria

Write $J(N)=\varphi(N)^{-1}\sum_{1<q\mid N}N^{2\eta_q}I_q(N;\eta_q)$. From (6), each of the following is sufficient at the stated strength.

1. **A real lower bound.** For some fixed $\delta>0$, $J(N)\ge -(1-\delta)\mathfrak S(N)$ for each sufficiently large even $N$ gives a prime representation there. More generally, $N(\mathfrak S(N)+J(N))$ need only dominate the independent remainder and the higher-prime-power contribution. For example a positive lower bound $\mathfrak S(N)+J(N)\gg N^{-1/2+\alpha}$ for any fixed $\alpha>0$ suffices by taking $\epsilon<\alpha$. The prime-power contribution is $\le 2(\psi(N)-\vartheta(N))\log N\ll\sqrt N\log^2(2N)$ by elementary counting and a Chebyshev bound. Upper deviations cost nothing for existence. With the actual count substituted on the right of (6) this is only a reformulation. The open estimate concerns the integrals in (4)–(5).
2. **One fixed wider line.** Define $B_q(\eta)=\int |K(s,t)E_q(s,t)|\,dx\,dy/(2\pi)^2$. A fixed $0<\eta<1/4$ and $B_q(\eta)\ll q^{1-\beta+\epsilon}$ with $2\eta<\beta\le1$ give $J(N)=o(1)$. Indeed $\sum_{q\mid N}q^{1-\beta+\epsilon}\ll N^{1-\beta+2\epsilon}$ and $N/\varphi(N)\ll_\epsilon N^\epsilon$. This needs no critical-line ratios, numerator disks or separate estimate for each parity. A wider line increases the needed saving. At $q\asymp N$, $\beta=2\eta$ gives only a constant-scale budget, whose signed constant would have to be controlled for positivity. Asymmetric lines have the analogous cost $N^{\eta_s+\eta_t}$.
3. **A qualitative conductor-local hypothesis.** Fix $c>0$ and for sufficiently large $q$ put $\eta_q=c/\log(2q)$. It suffices that
   \[
                         B_q(\eta_q)=o(\varphi^*(q)) \tag{7}
   \]
   as $q\to\infty$ through conductors with primitive characters. This gives $G(N)=N\mathfrak S(N)+o(N)$ for all even $N\to\infty$. To prove it, split at $q=N^{1/2}$. On small conductors put the integrals back on a fixed line $0<\eta_0<1/8$. The fixed-line GRH and model bounds of GWX §3 give $B_q(\eta_0)\ll_{\eta_0,\epsilon}q^{1+\epsilon}$. Their total contribution to $J(N)$ is $O(N^{-1/2+2\eta_0+O(\epsilon)})$. On the larger conductors $N^{2\eta_q}\le e^{4c}$, and $\sum_{q\mid N}\varphi^*(q)=\varphi(N)$ exactly. The supremum of the normalized errors (7) for $q>N^{1/2}$ tends to zero. Empty primitive families have $E_q=0$. This proves the claim. Replacing (7) by an $o(q)$ bound would require accounting for $\sum_{q\mid N}q/\varphi(N)$, which need not be bounded.

A signed version of (7) can be stated on large conductors alone: in this split, it suffices that the weighted real sum in $J(N)$ over $q>N^{1/2}$ be bounded below by $-(1-\delta)\mathfrak S(N)$, for fixed $\delta>0$. It allows cancellation between both heights and conductors. Condition (7) is stronger but does not depend on the target phases $N^{i(x+y)}$. It is a full-line condition on the differentiated, parity-weighted error for one fixed test. No transfer from Appendix A's families or unproved uniform tail bound is implicit in its formulation.

**A logarithmic-window formulation.** In (7) it suffices to bound the norm on $|x|,|y|\le D_0\log(2q)$ for any fixed $D_0>0$. To justify the tails at $\eta_q=c/\log(2q)$, $P_q(2\eta_q+i v)$ is bounded by $\sum_n\log^2(n)n^{-1-2\eta_q}\ll_c\log^3(2q)$. In (2.6) the product of $|F_p|$ for $p\nmid q$ is at most a fixed power of $\zeta(1+2\eta_q)$ times a constant, by $F_p=1+O(p^{-1-2\eta_q}+p^{-2})$. For $p\mid q$, $|1-p^{z-1}|\le1+e^{2c}/p$, and $q/\varphi(q)$ and this finite product cost at most fixed powers of $\log(2q)$ by the Euler product bound for primes. The pole at $z=0$ of $\zeta(1-z)$ costs $O(1/\eta_q)$ near zero and the zeta factor has polynomial height growth away from zero. Thus $H_q\ll_c\varphi^*(q)\log^{O_c(1)}(2q)(1+|x|+|y|)^C$ for nonempty families. The local zero bound below gives the same type of estimate for $A_q$. GWX (3.21)–(3.22) give $|K|\ll(1+|x|+|y|)^C e^{-|x|-|y|}$ uniformly on these lines for large $q$. The tails are $o(\varphi^*(q))$.

One can even state a sufficient hypothesis in terms of the two **untwisted** ratios before differentiation. Assume the errors in both instances of GWX (3.2), on the above box and the closed numerator disks of radius $r=\eta_q/8$ about the direct and reflected arguments, are uniformly
\[
 o\!\left(\frac{\varphi^*(q)}{(\log q)^3\log\log(3q)}\right).
\]
Then (7) follows. Here are the logarithmic costs. Put $v=x+y$. On the disks $\Re(a+b-1)\asymp\eta_q$ and $|\Im(a+b-1)-v|\le2r$. Hence the inverse sine in (3.4) is $O((\eta_q+\min(1,|v|))^{-1}e^{-\pi |v|/2})$. In the term $K/(h_0-h_1)$, the quotients $\Gamma(s)/\Gamma(a),\Gamma(t)/\Gamma(b)$ cost $O((2+|x|+|y|)^{O(r)})=O_c(1)$ on the box. In the term $K(h_0+h_1)/(h_0-h_1)$, the separate polynomial factors from $\Gamma(s)\Gamma(t)$ cost $O((2+|x|+|y|)^{2\eta_q})=O_c(1)$, and the exponential from the cosine is absorbed by theirs. In both cases the inverse gamma factor in $s+t$ cancels the inverse sine's exponential, leaving an integrable factor $O((1+|v|)^C e^{-|v|})$ from the remaining terms. Consequently the two weighted coefficients have total integral $O_c(\log q\log(2/\eta_q))$ on the box: integration transverse to $v$ has length $O(\log q)$, and the near-zero sine factor integrates to $O(\log(2/\eta_q))$. Cauchy's formula for the mixed derivative costs $r^{-2}$. Together these bounds give $o(\varphi^*(q))$ on the box; the direct logarithmic-derivative bounds handle the tails. This is one explicit sufficient rate on **disks**, with no uniformity in fixed $\omega_D$ required. Optimality of the logarithmic loss is open in this argument.

**Direct GRH attack on the differentiated, signed moment.** For every fixed $0<\eta<1/4$ one can reach the critical exponent:
\[
               B_q(\eta)\ll_{\eta,\epsilon}q^{1-2\eta+\epsilon}. \tag{7a}
\]
This improves on applying individual bounds after taking absolute values inside the character sum. Here is a derivation. In $A_q$ approximate the product of logarithmic derivatives by its double Dirichlet polynomial with multiplier $V(mn/Y)$, using the same $V$ as in (1). On the initial Mellin line its coefficients are $+\Lambda(m)\Lambda(n)\chi(m)\bar\chi(n)$. In the remainder integral shift the common shift $u$ to $-\eta+d$, $0<d<\eta$. There are no crossed $L$-poles for primitive $q>1$ under GRH. Taking absolute values *only in this remainder*, GWX (2.21) and Mellin decay bound it for the unnormalized family by
\[
       O_{d,\eta}\big(\varphi^*(q)Y^{-\eta+d}
                         \log^2(2q(2+|x|+|y|))\big).
\]
In the retained sum first apply primitive orthogonality **with** $\chi(-1)$. Its kernel on unit pairs is $\sum_{d_0\mid(q,m+n)}\mu(q/d_0)\varphi(d_0)$. In a box $m\asymp H, n\asymp K_0$ any contributing $d_0$ is $\ll\max(H,K_0)$, since $m+n>0$. The counting argument of (2) gives $O(HK_0/d_0)$ pairs. Both Mangoldt weights cost $O(\log^2(2Y))$. Summing over boxes and divisors gives
\[
      O_\eta\big(\tau(q)\log^4(2Y)Y^{1/2-\eta}\big)
\]
for the whole signed polynomial. Positivity of $m+n$ is essential here: in the untwisted sum $m=n$ is an integer diagonal for every $d_0$.

Set $Y=q^2$ and take $d$ sufficiently small in terms of $\epsilon$. Then $A_q\ll_{\eta,\epsilon}q^{1-2\eta+\epsilon}(1+|x|+|y|)^C$. The same bound holds for $H_q$ directly from (4): $|\Delta|\le2$, $P_q\ll_\eta1$, $C_q\ll_{\eta,\epsilon}q^\epsilon(1+|x|+|y|)^C$, and each gamma product contributes $q^{-2\eta}$ times a polynomial in heights. Integration proves (7a). The small loss can be made explicit for prime $q$ in the actual moment bound by taking $d=1/\log q$ for large $q$: the two log derivatives cost $O((\log q)^2\log^2(2q(2+|x|+|y|)))$ and the Mellin kernel stays a fixed distance from its pole for fixed $\eta$. The dyadic count then costs logarithms as displayed.

The two normalized error exponents for $Y=q^\nu$ in this direct calculation are $\nu\eta$ and $1-\nu(1/2-\eta)$, up to arbitrarily small losses. Their minimum has its exact maximum $2\eta$ at $\nu=2$. Taking a wider line changes this maximum and the detector cost by the same amount. In the balanced box $m,n\asymp q$, the congruence counts actual pairs with $m+n$ a specified multiple of a modulus of order $q$. The calculation bounded their total budget without computing their correlation.

Moreover the **model actually has this size**. For prime $p\to\infty$ and $s=t=\sigma=1/2+\eta$ fixed real, $H_p(\sigma,\sigma)/p^{1-2\eta}$ tends to a nonzero constant. Indeed $M_e(p)=p/2+O(1)$, $\Delta=-1$, $C_p(2\eta)\to C_1(2\eta)\ne0$ by GWX (2.3), (2.6) (the real zeta factor at $1-2\eta$ is nonzero). By the sine formula before GWX (3.11), the difference of the two scaled gamma squares contains $\sin^2(\pi\sigma/2)-\cos^2(\pi\sigma/2)=-\cos(\pi\sigma)\ne0$. Thus a triangle bound treating the two terms $A_p$ and $H_p$ independently cannot yield a pointwise $o(p^{1-2\eta})$ bound for $E_p$ on that window. The same obstruction applies to the absolute **separate** integrals: on a sufficiently small box of real heights around zero the modulus of $H_p/p^{1-2\eta}$ stays bounded below for large $p$. The common height phase of the two gamma products has modulus one, and after removing it the above convergence is uniform on the box by their explicit formulas. $K$ is continuous there with $K(\sigma,\sigma)>0$. This is a lower bound for the model norm, not for the true error or the signed integral.

On the moving line a simpler uniform comparison is informative. The local zero expansion gives $|D_\chi(1/2+\eta+ix)|\ll(1+\eta^{-1})\log(2q(2+|x|))$. Thus individual bounds on the actual sum, integrated against $|K|$, give $O(\varphi^*(q)(1+\eta^{-1})^2\log^2(2q))$ uniformly for $0<\eta<1/4$ (use Stirling for $K$). At $\eta=c/\log(2q)$ this costs $O_c(\varphi^*(q)\log^4(2q))$ before subtracting the model. Nor does the joint cutoff from (7a) supply a shrinking power here: for $Y=q^2$ the factor $Y^{-\eta}=e^{-2c+o(1)}$ stays positive. The signed correlation or cancellation against the model needed in (5) remains unestimated at the requisite precision.

## 6. Sparse conductor sets and the connection with the previous barriers

* For $N=2p$ with $p$ an odd prime, $\varphi^*(1)=1$, $\varphi^*(2)=\varphi^*(2p)=0$, $\varphi^*(p)=p-2$, and $\varphi(2p)=p-1$. Thus $J(2p)=(2p)^{2\eta_p} I_p(2p;\eta_p)/(p-1)$ exactly. On the units the only nonprincipal primitive family has conductor $p$; the imprimitive Euler factor at two has already been accounted for in (6). On a fixed line the $o(N)$ error test here is exactly $I_p(2p;\eta)=o(p^{1-2\eta})$. The existence test permits a negative contribution of order $p^{1-2\eta}$ with a controlled constant. A dyadic average over all $q$ permits an isolated conductor error of this size. **Existence at $2p$ itself is automatic from $p+p$**, with weight $(\log p)^2$ in $G(2p)$. This sequence tests the asymptotic and the proposed uniform proof mechanism. For nontrivial existence examples the same sparse phenomenon occurs at $N=2p^2$: the top conductor $p^2$ carries $(p-1)^2/[p(p-1)]=1-1/p$ of the mass, and $N/2$ is composite.
* For $N=2^k$, $k\ge2$, $\varphi(N)=2^{k-1}$, $\varphi^*(2^j)=2^{j-2}$ for $2\le j\le k$, with the remaining character of conductor one. The top conductor has share $1/2$, the next $1/4$ if present, and the top $r\le k-1$ together have share $1-2^{-r}$. Explicitly $J(2^k)=\sum_{j=2}^k 2^{j-k-1}N^{2\eta_{2^j}} I_{2^j}(N;\eta_{2^j})/\varphi^*(2^j)$. Exact cancellation between these errors could help. An average over a growing number of equally significant independent conductors is unavailable. The whole sparse sequence of powers of two can be exceptional in a usual dyadic mean.

For the relation to the repository's minor-arc analysis, its $F_N(\mathbb T)$ is exactly $e^{-1}G(N)$. If $\mathcal A$ is its chosen set of major arcs, then (6) yields
\[
 eF_N(\mathbb T\setminus\mathcal A)
 =N J(N)+N\mathfrak S(N)-eF_N(\mathcal A)+O_\epsilon(N^{1/2+\epsilon}).
\]
This specifies both the common unknown coefficient and the difference in the independently modeled terms. In that report the mean-square budget $1600N^{5/2}\log^3N$ permits a single error of size $N$ at a specified frequency. At $N=2p$ the ratios projection selects one primitive family and likewise requires a signed estimate at a specified target. The objects on the two sides are not term-by-term identical.

The sieve countermodel in the same report matches the squarefree divisibility tests up to all fixed levels below one and can have zero prime mass. It does not satisfy a proved ratios model. The $\chi(-1)$ here implements **reflection** in a group of residues; the sieve's Liouville sign measures the parity of the number of prime factors. Their relationship is the missing correlation of $\Lambda(m)$ with $\Lambda(N-m)$, not an equality of those two signs. In particular, the exact singular-series projection sums **model coefficients**. Applying it to the unknown signed ratios errors as though they had those model coefficients would assume the missing information.

## 7. A finite-endpoint version of the signed criterion

There is an exact way to use a finite verification without explicit constants in (6). Keep the induced Euler factors in the unknown moment. Let $A_{q,N}$ be (4)'s actual sum with each primitive character replaced in its logarithmic derivatives by its induced character modulo $N$. Let $I_{q,N}^{\rm ind}$ be (5) with $E_q=A_{q,N}-H_q$. Define the known baseline
\[
 \mathcal B(N)=\frac1{\varphi(N)}
 \left[
 \iint_{(5/4)^2} N^{s+t}K(s,t)D_{\chi_0}(s)D_{\chi_0}(t)
                   \frac{ds\,dt}{(2\pi i)^2}
 +\sum_{1<q\mid N}\iint_{(1/2+\eta_q)^2} N^{s+t}K(s,t)H_q(s,t)
                   \frac{ds\,dt}{(2\pi i)^2}
 \right],
\]
where $\chi_0$ is the principal character modulo $N$, with $L(s,\chi_0)=\zeta(s)\prod_{p\mid N}(1-p^{-s})$. The product-line notation means two upward vertical integrals. The principal term evaluates a specified one-function expression and the remaining terms use only the explicit model. The same residue and projection calculations in §4 give $\mathcal B(N)=N\mathfrak S(N)+O_\epsilon(N^{1/2+\epsilon})$ independently of a ratios bound.

The exact unit-restricted von Mangoldt count is
\[
 G_{\rm unit}(N)=\mathcal B(N)
       +\frac{N}{\varphi(N)}\sum_{1<q\mid N}N^{2\eta_q} I_{q,N}^{\rm ind}(N;\eta_q).
\]
Indeed, expand every logarithmic derivative on $5/4$, apply character orthogonality and the detector, and move only the nonprincipal contours. Their finite Euler factors have no poles in the intervening open half-plane under GRH. Add and subtract $H_q$. This argument uses no unknown big-$O$ constant. A sufficient one-sided inequality for **every** even $N>C=4\cdot10^{18}$ with $N/2$ composite is
\[
 \frac{N}{\varphi(N)}\sum_{1<q\mid N}N^{2\eta_q} I_{q,N}^{\rm ind}(N;\eta_q)
   > 2(\psi(N)-\vartheta(N))\log N-\mathcal B(N). \tag{8}
\]
The repository's finite verification covers the lower interval, and $N/2$ prime gives its own representation. The nuisance budget in (8) counts at most two choices for the coordinate that is a proper prime power, with the other coordinate weighted at most $\log N$. One may substitute the smaller exact unit-restricted proper-power contribution. At that exact threshold the assertion is equivalent to positivity of the unit prime-pair count, so it supplies no independent route to the inequality. Conditions (2), (6) and (7) identify where an independently provable analytic estimate would enter. No available input here establishes (7) or (8).

**Sources and scope.** GWX references are to the locally inspected v1, especially Hypothesis 1.1, (2.1)–(2.7), Proposition 2.1, §§3.1–3.6 and the opening of Appendix A. The Pascadi and other November comparisons use their supplied statements. No local Pascadi full text was located, so no additional theorem about its conductor range is attributed to it. The estimates above bound the tested deductions. They give neither a logical separation of Goldbach from Grand RH nor an optimality claim over all possible uses of Kloosterman sums. [Cached GWX PDF](/tmp/gou_wang_xu_2611.pdf) · [Repository pointwise and parity analysis](/home/nisbenz/.t3/projects/weak-goldbach/proof/strong_goldbach_research.md)

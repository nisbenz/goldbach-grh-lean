# Binary Goldbach at the critical conductor exponent

**Result.** I obtain an exact arithmetic expression for the error after subtracting the differentiated Gou–Wang–Xu (GWX) model inside a test sum. Its leading residual on each line of fixed sum is the weighted prime-pair count minus the integral of the Goldbach singular-series density on that line. There are explicit corrections on the diagonal and on lines of fixed difference. Both corrections vanish for the top conductors of \(2p^2\) and \(2^k\), \(p\) odd and \(k\ge3\). A modified detector at \(2^k\) isolates this residual in **one** conductor, with no analytic error term.

The fixed-conductor mollifier question has different answers at different accuracies. For fixed denominator shift \(\eta>0\), Track 2 already implies an additive power saving relative to the family size for every fixed polynomial length \(q^\theta\) with its specified Möbius coefficients. The critical Goldbach accuracy is stronger. Pascadi's Selberg-conditional \(8/15\) is a height-aspect exponent. The fixed-conductor Poisson calculation below exhibits a conductor multiplier in precisely the term of his bound that survives Selberg. I obtain no maximal conductor length at Goldbach accuracy.

There is a small arithmetic gain on the sieve side. Li–Liu's quantitative counts survive an explicit narrowing to \(a=1.8999998\) unconditionally and \(a=1.39998\) under their additional weighted Elliott–Halberstam hypothesis. The first number is weaker than the \(1.894\) improvement they describe in a remark. The argument gives a continuity bound for their count and a quantitative Möbius-bias criterion on the narrower sets. None of these estimates establishes positivity for two primes for every even target.

All references below are to the three local reports and four supplied manuscripts, in the versions listed at the end. Results from the manuscripts are used as stated. Grant Dirichlet GRH, the indicated Artin and automorphic RH hypotheses, Ramanujan–Petersson and Selberg as in Track 1. Most deductions below use fewer assumptions. GWX's ratios hypothesis and Li–Liu's \(\mathrm{WEH}(0.999)\) are identified separately wherever relevant. Write \(\mathfrak S(h)=0\) for odd \(h\) and use the usual ordered binary singular series for even \(h\). All asymptotic estimates about even targets concern sufficiently large integers.

## 1. Subtracting the model on the arithmetic side

Use \(A_q,H_q,E_q=A_q-H_q,P_q,C_q,X_{q,e},M_e,\Delta=M_0-M_1\) as in Track 2 (4), with \(q>1\), \(\phi^*=M_0+M_1\), \(s=\sigma+ix,\ t=\sigma+iy,\ \sigma=1/2+\eta,\ 0<\eta<1/4,\ z=s+t-1\). Here \(H_q\) always denotes the **differentiated parity model**. Define
\[
 b_q(h)=\sum_{d\mid(q,h)}\mu(q/d)\varphi(d),\qquad
 k_q(h)=\frac{q}{\varphi(q)^2}c_q(h)\prod_{\ell\nmid q}\sigma_\ell(h),
\]
where \(c_q\) is the Ramanujan sum and \(\sigma_\ell\) the local factor of \(\mathfrak S\). A useful conductor-by-conductor consequence of GWX Proposition 2.1 is
\[
                 \phi^* k_q(h)=b_q(h)\mathfrak S(h).                 \tag{1}
\]
Indeed apply divisor Möbius inversion in \(N\) to their (2.12), with \(h\) held fixed. This avoids division by a vanishing local factor or by an empty family size.

For a smooth compactly supported test \(W(u,v)\) in the open positive quadrant, use physical, unscaled coordinates and put
\[
\begin{split}
 G_{q,W}(h)&=\sum_{\substack{m+n=h\\(mn,q)=1}}\Lambda(m)\Lambda(n)W(m,n),\\
 F_+(h)&=\int_0^h W(u,h-u)\,du,\\
 F_-(h)&=\int_0^\infty \{W(u+h,u)+W(u,u+h)\}\,du,\\
 [T,W]&=\iint_{(\sigma)^2}T(s,t)\widetilde W(s,t)\,\frac{ds\,dt}{(2\pi i)^2}.
\end{split}
\]
The tilde denotes the double Mellin transform with powers \(u^{s-1}v^{t-1}\). Endpoints and integer diagonals have different measures in these definitions.

**Exact subtraction theorem.** Under Dirichlet GRH,
\[
\begin{split}
 [E_q,W]={}&\sum_{h\ge1} b_q(h)\{G_{q,W}(h)-\mathfrak S(h)F_+(h)\}\\
 &-\Delta\sum_{(j,q)=1}\Lambda(j)^2 W(j,j)
   -\Delta\sum_{h\ge1} k_q(h)F_-(h).                               \tag{2}
\end{split}
\]
There is no estimate or conjectural substitution for a prime count in (2). The first sum includes the integer diagonal of the actual moment. Its weight at \(m=n=j\), \((j,q)=1\), is \(b_q(2j)=b_q(2)=\Delta\), so the second term cancels that diagonal exactly. Removing those pairs and the second term gives an equivalent off-diagonal formula. In particular a one-prime progression density alone does not generate the reflected part of \(H_q\).

**Proof.** Shift the \(A_q\) contours to \(5/4\) under GRH, expand the two logarithmic derivatives and use primitive orthogonality on units. This gives \(\sum_h b_q(h)G_{q,W}(h)\). The test has rapid decay in the two heights and the primitive characters at \(q>1\) are nonprincipal. The \(\Delta P_q\) term gives the integer diagonal by absolute convergence. For the rest write \(C_q(z)=\Xi(z)D_q(z)\) as in GWX (2.4)–(2.6). With \(X_eX_e\) denoting \(X_{q,e}(s)X_{q,e}(t)\), the two identities needed are
\[
\begin{split}
 \tfrac12(X_0X_0-X_1X_1)\Xi(z)&=q^{-z}B(1-s,1-t),\\
 \tfrac12(X_0X_0+X_1X_1)\Xi(z)&=q^{-z}\{B(1-s,z)+B(1-t,z)\}.       \tag{3}
\end{split}
\]
The first is GWX (3.11). For the second insert their sine formula for \(X_{q,e}\). The sum of sine products gives \(\cos(\pi(s-t)/2)\). Use \(2\cos(\pi z/2)\cos(\pi(s-t)/2)=\sin(\pi s)+\sin(\pi t)\) and gamma reflection. The coefficients of the first and second lines in the model are \(\phi^*\) and \(\Delta\), respectively.

The integrals of \(u^{-s}v^{-t}\) over \(u+v=h\) and over the two positive rays \(|u-v|=h\), with the measures above, are \(h^{-z}\) times the respective beta expressions. For example \(\int_0^\infty u^{-s}(u+h)^{-t}du=h^{-z}B(1-s,z)\). These integrals converge since \(\Re s,\Re t<1\) and \(\Re z>0\). Equivalently, Mellin inversion in \(s\) with \(t=1+z-s\) gives \(\widetilde F_\pm(z)\) after multiplying \(\widetilde W\) by the corresponding beta kernel and integrating in \(s\). This follows by ordinary Mellin convolution on each ray, or by inverting \(W\) on the two lines and applying the preceding integrals. The beta functions grow at most polynomially on these contours. Compact support and smoothness justify the integrations. \(F_-\) can be nonzero at zero, so its Mellin strip here starts at \(\Re z>0\).

The model integrals are therefore the single integrals of \(q^{-z}D_q(z)\widetilde F_\pm(z)\). Shift **these** from \(2\eta\) to \(3/2\). The pole of \(\zeta(z)\) at one is canceled for \(q>1\). The transforms decay rapidly on the strip, and the arithmetic product has polynomial growth there. GWX (2.11) now gives \(\sum_h k_q(h)F_\pm(h)\). Using (1) in the sum term proves (2). This order of operations matters since the series for \(D_q\) need not converge absolutely on the original line.

The same proof applies to \(W(u,v)=w((u+v)/N)\) for the exponential, exponential times polynomial, and exponentially damped sinc-squared weights below. The transform is \(N^{s+t}B(s,t)\widetilde w(s+t)\). Smoothness and exponential decay on the real half-line, bounded derivatives at zero, Stirling for the beta factor and integration by parts in \(\widetilde w\) give rapid decay on the required positive strips. In this case \(F_+(h)=h w(h/N)\) and \(F_-(h)=\int_h^\infty w(u/N)\,du\), by substitution on the two rays. Both have the required decay. No application of an undifferentiated ratios conjecture is needed for these identities.

### The product cutoff and its remainder

Here is an exact way to apply (2) to **the polynomial in Track 2 (7a)** at specified complex shifts \(s_0,t_0\). Take a smooth \(\rho\) equal to zero up to \(1/2\) and one from 1 onwards. Put
\[
 W_Y(u,v)=\rho(u)\rho(v)u^{-s_0}v^{-t_0}V(uv/Y).
\]
This is a compact test since \(V\) vanishes beyond 2. Its lattice values reproduce every term of the polynomial. For \(0<d<\eta\), put
\[
 {\cal T}_Y=\int_{(-\eta+d)}\widetilde V(\xi)Y^\xi
                    A_q(s_0+\xi,t_0+\xi)\,\frac{d\xi}{2\pi i}.
\]
Common-shift Mellin inversion gives \([A_q,W_Y]=A_q(s_0,t_0)+{\cal T}_Y\). Consequently the exact remainder for the **untruncated** observable is
\[
 E_q(s_0,t_0)=[E_q,W_Y]
              +\{[H_q,W_Y]-H_q(s_0,t_0)\}-{\cal T}_Y.              \tag{4}
\]
All finite off-diagonal residuals are given by (2), and the braces are explicit from (1)–(3). The dependence of the continuous interpolation on \(\rho\) cancels in (4). One cannot identify a smoothed finite progression main term with an untruncated meromorphic model without this correction. The GRH allowance on \({\cal T}_Y\) is that of Track 2, \(O_{\eta,d}(\phi^*Y^{-\eta+d}\log^2(2q(2+|\Im s_0|+|\Im t_0|)))\). At \(Y=q^2\) it too is at critical power. Subtracting the model inside the polynomial repairs the separation of its main terms. A saving on the polynomial alone, while leaving this tail at its individual allowance, would still be insufficient.

One can instead smooth the **already subtracted** holomorphic \(E_q\) in the common shift. Start its Mellin integral against \(\widetilde V(\xi)Y^\xi\) on \(0<\Re\xi<1/4-\eta\), and shift to \(d-\eta\). The crossed residue is precisely \(E_q(s_0,t_0)\). This defines an analytic smoothing, which need not equal the finite physical-box smoothing above. The pointwise bound in the proof of Track 2 (7a) on the new line gives remainder \(O(q^{1-2d+\epsilon}Y^{-\eta+d}(1+|\Im s_0|+|\Im t_0|)^C)\). At \(Y=q^2\) the exponent is \(1-2\eta\) for **every** choice of \(d\). Inserting the critical estimate recursively after subtraction gives no power improvement either. For \(Y>q^2\) it does reduce the tail, at the cost of estimating a longer retained smoothing.

There is a repair for that tail **after projection**. Use induced characters modulo \(N\), sum over their primitive conductors before estimation, and take the original GWX detector. The arithmetic sum then has \(N\mid m+n\), and its nonzero terms have \(m+n=N\). On all these terms \(mn\le N^2/4\). Inserting the common cutoff \(V(mn/Y)\) with \(Y=N^2/4\) changes the projected actual count by exactly zero. This is an arithmetic cancellation of the entire cutoff error including the principal character in the projection. What survives is the residual on the single line \(h=N\). A balanced box \(m,n\asymp N\) meeting that line has expected weighted prime-pair mass on the order of \(N\) before the Dirichlet powers. At \(q\asymp N\) with \(|b_q(N)|\asymp q\), its allowed contribution after weighting by \(m^{-\sigma}n^{-\sigma}\) is of order \(q^{1-2\eta}\) if that expected density is missing on a fixed interior subinterval. This calculation describes a possible deficit, without asserting a density theorem for that interval.

## 2. Pascadi with Selberg and with the conductor held fixed

Write \(U\) for the common upper endpoint of the two inverse variables, \(A\) for the length of the third sequence and \(\vartheta\) for a fixed multiplier. The phase is \(e(\vartheta a\bar m/n)\) on \((m,n)=1\), with \(e(x)=\exp(2\pi i x)\). Theorem 1.1 bounds the bilinear operator norm by \(U^{11/12+o(1)}\) for \(0<|\vartheta|\ll U^{4/3}\). Theorem 1.2 bounds the trilinear sum by \(\|\alpha\|_2\|\beta\|_2\|\nu\|_2 U^{11/12+o(1)}A^{1/6}\) for \(\vartheta=1,\ A\ll U^{1/14}\). The following larger-frequency terms matter here.

* Corollary 4.9 bounds the bilinear norm by \(U^{o(1)}(U^{11/12}+U^{7/8}|\vartheta|^{1/32}+\sqrt{|\vartheta|})\).
* In Corollary 4.10 set Pascadi's exceptional-spectral parameter to zero. After extracting the three norms and \(U^{1+o(1)}\sqrt A\), its bound for \(\vartheta=1\) becomes
  \[
    \ll U^{-1/12}A^{-1/3}+U^{-3/28}A^{-1/7}+\sqrt A/U .
  \]
  The first two terms of the paper's four coincide under Selberg. The first displayed term dominates the second for \(A\le U^{1/8}\).
* With a multiplier, (4.13) before optimization gives a normalized bound, up to \(U^{o(1)}\), of
  \[
   \frac{\sqrt{|\vartheta|A}}{U}
    +\frac1{\sqrt{AL}}+\frac1{A^{1/4}L^{3/4}}
    +\frac L{U^{1/4}}\left(1+\frac{|\vartheta|A}{L^8}\right)^{1/16},
                   \qquad L\ge1.                                   \tag{5}
  \]
  This follows by removing the exceptional factor from that formula. In the Kuznetsov argument the \(X^{2\theta_f}\) losses from eigenvalues below \(1/4\) disappear. The regular spectral large sieve, the amplifier and the first term of (5) still occur. That first term is already present before the exceptional-spectrum estimate. An individual Lindelöf bound or Ramanujan bound for the forms does not remove it from the stated inequality.

In Pascadi §5.1 the zeta height integral gives \(|h\Delta|\ll T^{o(1)}N_1N_2/(d^2T)\), \(\vartheta=1\). In his calculation a normalized term \(U^{-s}A^{-t}\) costs \(T^{t+o(1)}Y^{2-s-2t}\). Under Selberg the first two distinct pairs are \((1/12,1/3)\) and \((3/28,1/7)\). They cost \(T^{1/3}Y^{5/4}\) and \(T^{1/7}Y^{45/28}\), respectively, both reaching \(T\) at \(Y=T^{8/15}\). The other terms \(T^{-1/2}Y^2\) and \(T^{1/2}Y^{1/2}\) are smaller there. Thus \(8/15\) is the supremum of the strict power-saving range in this calculation, exactly as stated after Theorem 5.1. Unconditionally its range is \(\sigma<207/389\). The theorem integrates zeta in height with shifts \(O(1/\log T)\).

### Two Poisson summations one can actually try on \(R_{q,M}\)

In Track 2's approximate functional equation let \(m,n\) be the smooth numerator indices, \(mn\lesssim q^{1+\epsilon}\), and \(r,v\) the two Möbius indices, \(r,v\lesssim M\). For clarity take \(q\) prime. The primitive parity projector includes \(mr\equiv\pm nv\bmod q\) and the principal subtraction. Poisson summation in \(m\) directly gives a phase \(e(\pm jnv\bar r/q)\). Reciprocity gives \(e(\mp jnv\bar q/r)e(\pm jnv/(qr))\). Applying the bilinear norm with the \(q\) index a singleton costs an upper endpoint at least \(q\). In the balanced numerator box \(m,n\asymp\sqrt q\), \(|j|\lesssim \sqrt q\,q^\epsilon\), and \(|jnv|\) reaches the scale \(qM\). A height-aspect small-frequency substitution here would use the wrong inverse variable.

A better match keeps **both** long Möbius indices inside the bilinear form. Consider the minus congruence and write
\[
                  mr-nv=kq .
\]
Restrict first to \((r,v)=1\), \(r,v\asymp M,\ m,n\asymp U_0=\sqrt q\), and \(q^{1/2}\le M<q/3\) with the supports inside \((0,q)\). This is an actual part of the primitive projector. For a smooth product cutoff \(f(m/U_0)g(n/U_0)\), eliminate \(m\), then Poisson-sum \(n\equiv-kq\bar v\bmod r\). The exact kernel is
\[
 \frac1r\sum_{h\in\mathbb Z}e(-hkq\bar v/r)
       \int_{\mathbb R} g(y/U_0) f((vy+kq)/(rU_0)) e(-hy/r)\,dy .  \tag{6}
\]
The plus congruence has the corresponding sign changes. The integer diagonal \(k=0\), the frequency \(h=0\) and the principal subtraction have to be kept when identifying a full main term. A common divisor \(d=(r,v)\) divides \(k\) here and rescales the determinant. Composite conductors also introduce all primitive-projector divisors. Failure to handle even the displayed nonzero-frequency box prevents a proof by this direct estimate.

Set \(B=M/\sqrt q\). Then \(|k|\ll B\) on the support and \(|h|\ll Bq^\epsilon\) up to rapid tails. On \(|k|,|h|\ll B\) the integral divided by \(U_0\), including the smooth factor \(M/r\), has bounded derivatives of any fixed order in the normalized \(r,v\) coordinates. Partial summation in each variable therefore permits Corollary 4.9 for fixed \(h,k\). Imaginary powers from the allowed logarithmic shifts cost logarithms in fixed derivatives. The two arithmetic coefficient norms after extracting their size are \(O(\sqrt M)\) each. The scalar size, including \(U_0/M\) from Poisson, the numerator powers \(1/U_0\), and the two denominator powers, is \(O(M^{-2-2\eta})\). Thus one normalized term of the moment has the bound
\[
 \ll M^{-2\eta+o(1)}
   \left(M^{-1/12}+M^{-1/8}|qhk|^{1/32}+\sqrt{|qhk|}/M\right).      \tag{7}
\]
The family normalization is by \(q\), canceling the congruence coefficient of order \(q\). This is a genuine saving from the new spectral estimate on subranges, for instance if \(|qhk|\ll M^{4/3}\) the parenthesis is \(O(M^{-1/12})\). In the outer nonzero ranges \(|h|,|k|\asymp B\), the scale is \(|qhk|\asymp M^2\). The last term then gives only a constant per pair. The smooth transforms need not decay by a power for frequencies at a fixed multiple of their natural length.

Grouping \(a=|hk|\) gives \(A\asymp B^2=M^2/q\) and multiplier \(\vartheta=q\). Smooth dyadic restrictions can be separated in the four normalized variables by Fourier inversion in their logarithms, with bounded cost on these boxes. The resulting product-index coefficients are bounded by the divisor function and have norm \(O(A^{1/2+o(1)})\). In (5) the term \(\sqrt{qA}/M\) still has constant size, whatever the amplifier length. Applying the \(\vartheta=1\) corollary to the sparse sequence supported at \(q|hk|\) instead uses upper endpoint \(qA\asymp M^2\) in its frequency variable. It again retains the term \(\sqrt{qA}/M\) and pays for the longer endpoint in the prefactor. For comparison, Pascadi's elementary Lemma 3.1, using \((q,r)=1\), gives norm bound \(O(M^{o(1)}\sqrt{M(M+A)})\) after the three coefficient norms. For \(A\le M\) the normalized box cost is \(O(M^{-2\eta+o(1)}\sqrt A)\), or \(O(q^{-1/2+o(1)}M^{1-2\eta})\). This recovers the power budget of Track 2 (2) on this box. These are bounds delivered by particular inequalities. They supply no lower bound for the actual Möbius-weighted frequencies.

One repair does work right at the transition. For \(M\asymp U_0=L=\sqrt q\), restrict to a separably smoothed equal-length determinant block with all four variables in \((L,2L]\) and fixed nonzero \(k=O(1)\). Pascadi Theorem 5.3 applies directly with \(\Delta=kq\), without imposing \((r,v)=1\). Its zero-frequency integral includes the sum over \((r,v)\mid\Delta\). At \(|\Delta|\asymp L^2\) the \(L^{19/20}\) branch in its minimum, credited there to Bettin–Chandee, is preferable. Since the coefficient norms are \(O(\sqrt L)\) after extracting denominator powers, the normalized error about **that integral** is
\[
             O(L^{-2-2\eta}L^{1+19/20+o(1)})
                   = O(q^{-\eta-1/40+o(1)}).
\]
Here one may take real shifts and fixed smooth numerator cutoffs, absorbing \(m^{-1/2},n^{-1/2}\) into the cutoffs after extracting their scale. The theorem has common length for the four variables and constants depending on the smooth weights. Replacing the scale \(L\) by a much longer mollifier scale shrinks the smooth supports and changes those constants. It also requires a sum over growing \(k\). This estimate for an actual subproblem does not evaluate the full moment or identify the complete GWX main term.

There is a further repair for the outer frequencies of (6) even when \(M>\sqrt q\). Use the classical Bettin–Chandee trilinear theorem cited by Pascadi as [BC18, Theorem 1]. In its balanced specialization the norm factor, apart from \(M^{o(1)}\) for \(A\) of fixed polynomial size, is
\[
 \left(1+\frac{|\vartheta|A}{M^2}\right)^{1/2}
       \left(M^{19/20}A^{7/20}+M^{7/8}A^{1/2}\right).
\]
The two terms come from \((AM^2)^{7/20}(2M)^{1/4}\) and \((AM^2)^{3/8}(2AM)^{1/8}\). Unlike the first term of (5), the multiplier here is a bounded *factor* when \(\vartheta=q,\ A\asymp M^2/q\). Applying this to the grouped, coprime block in (6), with norms \(O(M\sqrt A\,M^{o(1)})\) and the same outside factor \(M^{-2-2\eta}\), bounds its nonzero outer frequencies by
\[
 \ll M^{-2\eta+o(1)}
      \left(M^{-1/20}A^{17/20}+M^{-1/8}A\right)
 \ll q^{o(1)}
      \left(q^{-17/20}M^{33/20-2\eta}
                  +q^{-1}M^{15/8-2\eta}\right).
\]
In particular this subproblem has a power saving for
\(\theta<\min(17/(33-40\eta),\,8/(15-16\eta))\) in the stipulated range \(M\ge\sqrt q\), and already for \(\theta<17/33\) with the denominator damping omitted. This repairs the large-multiplier obstruction to a power saving on **this** balanced block. It is important to keep the gain: merely pointing at \(\sqrt{qA}/M\) in Pascadi's bound would miss it. The computation controls oscillatory terms about the Poisson zero frequency. A full ratios estimate must also combine the zero frequency with both primitive parity projectors and main terms, handle the unbalanced approximate-functional-equation blocks and composite-conductor divisors, and control the reciprocals at the required accuracy. Substituting \(17/33\) as a full conductor-aspect endpoint would skip those steps.

### What “maximum mollifier length” can mean

Denote by \(\mathcal M_q\) the full two-term ratios model and by \(D_{q,M}\) the finite integer diagonal from Track 2. Fix the critical numerator lines and their logarithmic height window, \(0<\eta<1/8\), and \(M=q^\theta\).

1. For the direct off-diagonal count around \(D_{q,M}\), Track 2 (2) gives \(o(q)\) for \(\theta<1/[2(1-2\eta)]\). This passes \(1/2\) for fixed \(\eta>0\). Equation (7) and the determinant calculation improve selected terms but provide no improved endpoint for the complete direct estimate here.
2. For the **specified reciprocal Möbius coefficients** there is actually **no finite maximal fixed \(\theta\)** for an \(o(q)\) approximation on these lines. Indeed Track 2's joint-product cutoff gives \((R_q-\mathcal M_q)/q\ll q^{-\eta+\epsilon}\). Its individual reciprocal bound gives \((R_{q,M}-R_q)/q\ll q^{-\theta\eta+\epsilon}\) for each fixed \(\theta>0\). Thus
   \[
    (R_{q,M}-\mathcal M_q)/q
            \ll_{\theta,\eta,\epsilon}q^{-\min(\eta,\theta\eta)+\epsilon}.       \tag{8}
   \]
   Track 2 (3), taking its \(h<\eta\) close enough to \(\eta\), gives the same bound for \((R_{q,M}-D_{q,M})/q\). The latter conclusion estimates the finite off-diagonal indirectly, using the fact that the coefficients approximate reciprocals. It says nothing of this strength for arbitrary twisting coefficients. At this accuracy \(1/2,1,2\) and all larger fixed lengths are allowed.
3. For a normalized saving **exceeding \(2\eta\)** in the differentiated detector, (8) only certifies a saving up to \(\eta\) even before differentiation and parity inversion. Substitution alone by the individual fixed-distance GRH inequality would need \(\theta>2\) for that stronger power budget. Controlling substitution and evaluating the longer polynomial with comparable precision are separate tasks. No cited Pascadi theorem determines a sharp \(\theta_{\max}\) at the required conductor accuracy, for prime or all composite conductors. Nor is \(8/15\) such an upper bound. There is even a precise transfer at a prescribed numerator-line accuracy. For fixed \(\omega>0\) and \(\theta\eta\ge\omega\), a bound \(O_\epsilon(q^{1-\omega+\epsilon})\) about \(\mathcal M_q\) for \(R_{q,M}\) is equivalent to the same bound for \(R_q\), by the individual substitution estimate in both directions. Thus once a polynomial is long enough for that accuracy, length by itself cannot settle the remaining ratios question. At \(\eta=c/\log q\) the implied constants and the fixed-power savings in (8) cannot be used to deduce Track 2 (7).

## 3. Signed and positive-definite tests

Normalize \(w(1)=1\). For any absolutely convergent real test on the multiples of \(N\) with \(w(k)\le0\) for \(k\ge2\), positivity of \(\Lambda\) gives
\[
  T_w(N):=\sum_{k\ge1}w(k)G(kN)\le G(N),\qquad
  M_w(N):=N\sum_{k\ge1} k\,w(k)\mathfrak S(kN)\le N\mathfrak S(N). \tag{9}
\]
Here \(G(h)=\sum_{m+n=h}\Lambda(m)\Lambda(n)\). For a proof with this minorant, its positive lower bound must also exceed the proper-prime-power contribution at \(N\). The second inequality tracks the cost on the model of relaxing exact interpolation.

For example \(w_b(v)=(2-v)e^{-b(v-1)}\) is entire, \(w_b(2)=0\), and \(w_b(k)<0\) for \(k\ge3\). It gives
\[
  0\le 1-\frac{M_{w_b}(N)}{N\mathfrak S(N)}
        \le \sum_{k\ge3} k(k-2)\tau(k)e^{-b(k-1)}
        =O(e^{-2b})\qquad(b\ge1).
\]
This uses the local Euler factors, as in GWX (3.15). The signed detector can thus retain arbitrarily nearly the entire projected main term. Its physical kernel has rank at most two, obtained by expanding \((2-u-v)e^{-b(u+v-1)}\). This simplification has no bearing on the sign of the centered correlation. More generally the exact signed discrepancy in (9) is \(\sum_{k\ge1}w(k)(G(kN)-kN\mathfrak S(kN))\). At the level of nonnegative coefficient data, even granting the exact model at **every other multiple**, a missing target coefficient gives discrepancy \(-N\mathfrak S(N)\) for every such test simultaneously. This is a test of a proposed positivity inference, not a sequence of Mangoldt coefficients.

**Two positivity obstructions.**

* A positive-semidefinite kernel \(w(u+v)\) on the positive real half-line obeys \(w(2u)\ge0\) and \(|w(u+v)|^2\le w(2u)w(2v)\). Thus \(w(2)\le0\) forces \(w(2)=0\), then \(w(1+v)=0\) for every \(v>0\). Continuity at 1 contradicts \(w(1)=1\). This excludes the whole positive-semidefinite sum-kernel proposal, including the choice with all unwanted integer values zero. A common continuous \(w\) positive at 1 also cannot be nonpositive at all \((N\pm1)/N\) for unbounded \(N\) without first projecting onto multiples. A test depending on \(N\) can separate that finer grid, at the cost of varying its transforms.
* A separable Mellin weight can genuinely produce a squared norm **within** each character. For instance a real physical profile \(f\) on both coordinates gives \(Z_\chi=\sum_n\Lambda(n)\chi(n)f(n/N)\) and the primitive contribution \(\sum_{\chi\ \mathrm{even}}^*|Z_\chi|^2-\sum_{\chi\ \mathrm{odd}}^*|Z_\chi|^2\). A sum of positive rank-one kernels gives the same difference of positive forms. Positivity of either parity norm supplies no ordering of the two. Independently of Mellin conventions, reflection on units has eigenvalues \(+1,-1\) and \(\langle f,Rf\rangle=\|f_+\|^2-\|f_-\|^2\). For the circle method the coefficient is a square of a Fourier transform with a target phase. Conjugating one factor to produce a positive norm changes the additive statistic to a difference. The reflection-hole example realizes total cancellation of the main contribution even with small individual Fourier coefficients. Section 5 below localizes this example to the largest primitive conductor.

There is nevertheless a positive-semidefinite **two-variable** detector that isolates the correct line. Choose real \(0\le f\le1\) in \(C_c^\infty((1/4,3/4))\), symmetric about \(1/2\), and \(W(u,v)=f(u/N)f(v/N)\). This is rank one. Its sum coordinate lies strictly between \(N/2\) and \(3N/2\). At \(N=q=2^k,\ k\ge3\), only \(h=N\) survives even the primitive projector, and (2) becomes
\[
 \frac{[E_N,W]}{\varphi^*(N)}
   =\sum_{\substack{m+n=N\\(mn,N)=1}}
        \Lambda(m)\Lambda(n) f(m/N)^2
      -N\mathfrak S(N)\int_0^1 f(u)^2\,du .
\]
Here the *actual* integrated moment is nonnegative. The first term would have to be bounded below by a positive fraction of the second to obtain the requested margin. At \(N=8\), take nonzero \(f\) supported in \((7/16,9/16)\). The only integer in the scaled interval is 4, a nonunit. The centered moment therefore attains the full negative of the model **exactly**, with true Mangoldt coefficients and a positive-semidefinite test. There is also an obstruction to uniformity over tests varying without derivative bounds: replace a fixed nonzero \(f\) above by \(f(u)\sin^2(\pi Nu)\). All integer samples vanish, whereas the integral of the squared profile tends to \((3/8)\int f^2>0\) by the Riemann–Lebesgue lemma. This last example addresses test-uniform claims only. A useful fixed smooth interior profile at large \(N\) still poses the arithmetic lower-bound problem. Compact smooth tests are admissible in (2) for the differentiated observable, while applying GWX's exponentially ill-conditioned inversion from undifferentiated ratios requires additional height decay.

**A sign check with actual primes.** Define the entire test
\[
 w_c(v)=e^{20(1-v)}
       \left(\frac{\sin(\pi c(v-1))}{\pi c(v-1)}\right)^2,
            \qquad c\in\mathbb Z_{>0}.                               \tag{10}
\]
It is one at 1 and vanishes at the other positive multiples of \(1/c\). Use \(I_q^w\) for Track 2 (5) with that weight. For \(N=q=2^k,\ k\ge3\), \(\Delta=0\) and \(b_q(h)=\varphi(q)1_{q\mid h}-\varphi(q/2)1_{q/2\mid h}\). With \(c=2\) the only contributing \(h\) in (2) is \(N\). The unit restriction deletes exactly the ordered pair \((2^{k-1},2^{k-1})\) among nonzero-weight pairs of even integers summing to \(2^k\), by taking their 2-adic valuations. Hence
\[
 \boxed{\quad
 \frac{N^{1+2\eta}}{\varphi^*(N)} I_N^{w_2}(N;\eta)
       =G(N)-(\log 2)^2-N\mathfrak S(N).
 \quad}                                                            \tag{11}
\]
In particular at \(N=8\) the unit count is \(2\log3\log5<8\), whereas \(\mathfrak S(8)\ge2(1-\sum_{j\ge1}(2j)^{-2})>1\). The integrated error is strictly negative. Equation (11) tests real integration *before* estimation and allows arbitrary vertical oscillation. At any missing prime target its right side would be \(-N\mathfrak S(N)+O(\sqrt N\log^2(2N))\). The finite sign example disproves automatic nonnegativity for this admissible detector. It does not disprove an asymptotic lower margin for genuine primes.

There is a variable-test counterpart for \(N=2p^2,\ q=p^2,\ p\) odd prime. Here \(b_q\) is supported on multiples of \(p\), \(\Delta=0\), and (10) with \(c=2p\) isolates \(h=N\). The deleted pair is exactly \((p^2,p^2)\), by its \(p\)-adic valuation. The analogue of (11) has \(N^{1+2\eta}I_{p^2}^{w_{2p}}/\varphi^*(p^2)\) on the left and \((\log p)^2\) in place of \((\log 2)^2\) on the right. This identity is exact for each \(p\). The scale of the oscillations in \(w_{2p}\) grows with \(p\), so a uniform bound proved for the original fixed test cannot be transferred to it. Individual-conductor sign and error questions remain arithmetic even when a weight isolates the desired target perfectly.

## 4. The unbalanced convolution theorem and the sieve count

Let \(x\asymp MN_s\) denote Pascadi's convolution scale, with short factor of length \(N_s\). His Theorem 5.2 is an absolute sum of progression discrepancies over \(q\sim Q,\ (q,a)=1\), at **one fixed residue integer** \(a\), for divisor-bounded \(\alpha_m,\beta_n\), with \(\beta\) Siegel–Walfisz, \(\exp((\log x)^\epsilon)\le N_s\), \(0<|a|\le x/12\). The dyadic product is also restricted by \(x<mn\le2x\). Up to the \(x^{-\epsilon}\) margin, the three upper bounds on \(Q\) are
\[
 (x^{207}/N_s^{468})^{1/389},\qquad
 (x^{151}/(|a|^8 N_s^{292}))^{1/277},\qquad
 x^{3/4}/(|a|^{1/4}N_s).                                          \tag{12}
\]
For the small residues in Corollary 1.4 the first suffices. Even there a gain beyond \(1/2\) from that bound requires \(N_s=x^\nu\) with \(\nu<25/936\). At \(\nu=2/9\) the first exponent is \(103/389\). In particular inserting Track 1's marked prime as this short factor fails the exponent test. In a direct application with \(a=N\) and products up to \(N\), the size restriction on \(a\) already fails. Even a comparable target-sized residue within the admissible constant range makes the third bound \(O(x^{1/2}/N_s)\). Reducing \(N\) to a small representative separately for each modulus changes the fixed-residue hypothesis.

One can check the possible Selberg improvement directly in the proof. In the branch \(N_s\le X^{1/53},\ X=MN_s\), the final factor \((1+X^7/(N_s^{20}Q^{13}))^{7/128}\) on p. 49 disappears. With the author's \(L=X^\delta N_s^2H,\ H=Q^2/M\), the remaining increasing term, apart from \(X^\delta\), is
\[
 \frac{N_s^{19/4}Q^{15/4}}{X^2}
       \left(1+\frac{|a|X^7}{N_s^{22}Q^{14}}\right)^{1/16}.
\]
The corresponding two strict power conditions are \(N_s^{19}Q^{15}<X^8\) and \(|a|N_s^{54}Q^{46}<X^{25}\), each with a fixed power margin. The third restriction in (12) comes from a different term and is unchanged. The remaining dispersion errors require, in particular, \(Q\le M X^{-c}\) for some \(c>0\), which holds in these small-factor ranges with the displayed margins. This is a specialization of the small-factor branch, with its original coefficient, residue, smoothness and short-factor hypotheses. For \(N_s\ge X^{1/53}\) the paper invokes a different theorem of Fouvry. Extending the small-factor calculation to general \(N_s\) by changing the exceptional eigenvalue parameter would be unjustified.

Li–Liu use different estimates at different stages. Their Theorem 1.1 gives \(D_{1,1.9}>0.0004 C(N)N/\log^2 N\); Theorem 1.3 gives \(D_{1,1.4}>0.062 C(N)N/\log^2 N\) under \(\mathrm{WEH}(0.999)\), where \(C(N)=\mathfrak S(N)/2\). \(D_{1,a}\) counts \(p\) with \(N-p=rq'\), \(q'\) prime, \(r=1\) or \(r\) prime and \(r\le(q')^{a-1}\). For \(a<2\) every allowed composite is squarefree with a unique smaller factor \(r\). In their §§4–5 the lower sieve uses \(\{N-p\}\), and the upper and switched sieves also use sequences with a *specified* prime divisor. For example §8.2 compares the lower term \(G_1\) at \(N^{4/53}\) with \(G_3=\sum_{N^{9/19}\le r\le N^{1/2}}S(\mathcal A_r;\mathcal P(N),r)\). Their conditional input includes maxima over reduced residues and variable cutoffs in sums of weighted prime remainders. A fixed-residue estimate for a short-factor convolution does not give these inequalities. Their Lemma 3.3 citing earlier Pascadi work concerns well-factorable **upper** sieve weights and the authors explicitly explain its inapplicability to the needed terms. It is a different result from (12).

### A continuity bound that really does narrow the exponent

Let \(L_N=\log N,\ \tau(a)=(a-1)/a\). For fixed \(1<b<a<2\), the following bound needs no RH assumption:
\[
 \limsup_{\substack{N\to\infty\\2\mid N}}
 \frac{(D_{1,a}(N)-D_{1,b}(N))L_N^2}{\mathfrak S(N)N}
 \ \le\ \frac{200}{(1-\tau(a))^2}\log\frac{\tau(a)}{\tau(b)} .     \tag{13}
\]
The constant is deliberately loose. The point is that a quantitative lower margin for \(D_{1,a}\) pays for a concrete left-neighborhood of \(a\).

**Proof.** Discard \(m=N-p<N/L_N^4\) at a cost \(O(N/L_N^4)\). A witness lost in narrowing must be composite. Since \((q')^{b-1}<r\le(q')^{a-1}\) and \(m=rq'\), its smaller prime lies in
\[
                  (N/L_N^4)^{\tau(b)}<r\le N^{\tau(a)} .
\]
If \(r\mid N\), then \(p=r\), accounting for at most \(\omega(N)\) choices. Fix any other prime in the displayed range and put \(X=N/r\). Bound the number of simultaneously prime \(n,N-rn\), \(1\le n<X\). At primes \(\ell\mid Nr\) there is one excluded residue of \(n\) and at other primes there are two. This follows also at \(\ell=r\) because \(r\nmid N\). Write \(\nu_\ell\) for the number of exclusions and \(g_\ell=\nu_\ell/\ell\).

Here are details justifying a uniform sieve constant in (13). Use Selberg's elementary upper-bound quadratic sieve with \(z=X^{2/5}\), using only primes up to \(w=z^{1/3}\). For the sifted count the bound is
\[
 X/G(z)+O(z^{2+o(1)}),\qquad
 G(z)=\sum_{\substack{d\le z\\d\mid\prod_{\ell\le w}\ell}}
              \prod_{\ell\mid d}\frac{g_\ell}{1-g_\ell}.
\]
Indeed the squarefree divisor counts have remainder at most \(\prod_{\ell\mid d}\nu_\ell\) by CRT and interval counting. In the Selberg quadratic form the optimal coefficients are
\(\lambda_d=\mu(d)\prod_{\ell\mid d}(1-g_\ell)^{-1}G_d(z/d)/G(z)\), where \(G_d\) omits primes dividing \(d\). They have modulus at most one by inserting all divisors of \(d\) back into \(G(z)\). To see the minimum directly, write \(g(d)=\prod_{\ell\mid d}g_\ell,\ h(d)=\prod_{\ell\mid d}g_\ell/(1-g_\ell)\). The quadratic main form is \(\sum_k h(k)^{-1}(\sum_{k\mid d}\lambda_d g(d))^2\), since \(1/g((d,e))=\sum_{k\mid(d,e)}1/h(k)\). Divisor inversion and \(\lambda_1=1\) give the minimum \(1/G(z)\) by Cauchy–Schwarz with equality at the stated coefficients. With \(d,e\le z\) the total remainder costs at most \(z^2\max_{j\le z^2}2^{\omega(j)}=z^{2+o(1)}\). Candidate primes in either form of size at most \(w\) add \(O(w+1)\).

Normalize the unrestricted Euler sum for \(G\) to probability. Its random squarefree \(d\) includes each \(\ell\le w\) independently with probability \(g_\ell\), so \(\mathbb E\log d\le2\log w+O(1)\) by Mertens. Markov's inequality leaves at least \(1/3-o(1)\) of the mass at \(d\le z\). Moreover
\[
 \prod_{\ell\le w}(1-g_\ell)
 \le(1+o(1))\mathfrak S(N)\frac{r-1}{r-2}
             \frac{e^{-2\gamma}}{\log^2 w}.
\]
Divide each factor by \((1-1/\ell)^2\). The complete local product is \(\mathfrak S(N)(r-1)/(r-2)\). Omitting the tail costs at most the inverse of \(\prod_{\ell>w}(1-1/(\ell-1)^2)=1-o(1)\), uniformly in the bad primes. The prime 2 has a single exclusion and supplies the usual factor 2. Since \(\log w=(2/15)\log X\) and \(r\to\infty\) uniformly, the bound for the fixed \(r\) is at most \(200\mathfrak S(N)X/\log^2 X\) for all sufficiently large \(N\). All floor errors are uniform because \(X\ge N^{1-\tau(a)}\). Finally \(\log X\ge(1-\tau(a))L_N\), and the sum of \(1/r\) on the displayed interval tends to \(\log(\tau(a)/\tau(b))\) by Mertens. This proves (13).

For \(a=1.9,\ b=1.8999998\), the right-hand side is less than \(0.000085\), against Li–Liu's lower margin \(0.0002\) in singular-series units. For \(a=1.4,\ b=1.39998\), it is less than \(0.01401\), against the conditional margin \(0.031\). These strict inequalities also follow using \(\log x\le x-1\). For sufficiently large even \(N\) we obtain, respectively,
\[
 D_{1,1.8999998}(N)>0.00011\,\mathfrak S(N)N/L_N^2,\qquad
 D_{1,1.39998}(N)>0.016\,\mathfrak S(N)N/L_N^2
                        \quad(\mathrm{WEH}(0.999)).                  \tag{14}
\]
The unconditional manuscript already announces \(1.894\) by a double-sieve refinement. Equation (13) gives a different deduction directly from quantitative supply and a uniform two-prime upper sieve. Iteration of (13) spends that finite supply. As \(b\downarrow1\), the bound on the accumulated loss from a fixed \(a>1\) grows without bound. The same inequality with a finer partition has logarithmic divergence near \(\tau=0\).

For either permissible \(b\), let \(B_b=\sum_{p\ {\rm counted\ in}\ D_{1,b}}\mu(N-p)\). The ordered two-prime count is exactly \((D_{1,b}-B_b)/2\). Thus (14) gives explicit narrower baselines for Track 1 (9), with the indicated constants and hypotheses. Neither (13) nor (14) bounds the bias below its baseline. In particular (14) cannot be subtracted from the full Chen count as if the two sets were disjoint.

### How a prime-free model passes the narrowed supply test

The parity model in Track 1 (7) allows a more quantitative check here. In its notation \(a_m^+=K_0^{-1}w(m)(1+\lambda(m))\) and in fact
\[
                             K_0^{-1}=\mathfrak S(N).
\]
For each odd \(\ell\), \(1+1/(\ell(\ell-2))=(1-1/(\ell-1)^2)^{-1}\). Substitution in Track 1's formula for \(K_0\), including \(\varphi(N)/N\), proves the identity prime by prime. In particular \(a_m^+\ge2\mathfrak S(N)\) on semiprimes coprime to \(N\).

Use the synthetic mass \(a_m^+/\log N\) to compare with *unweighted* Chen-candidate counts. Take \(N^{1/4}<r\le N^{7/25}\) prime and \(N/(2r)<s\le N/r\) prime, omitting primes dividing \(N\). Then \(m=rs\) has a unique such factorization, is \(N^{2/9}\)-rough, and \(r\le s^{b-1}\) for both \(b\)'s in (14) once \(N\) is large. This last inequality follows from \(7/25<\tau(1.39998)\) and \(s>N/(2r)\). The total synthetic mass on just these semiprimes is at least
\[
    (\log(7/6)-o(1))\frac{\mathfrak S(N)N}{\log^2 N}.              \tag{15}
\]
Indeed the PNT uniformly on the dyadic \(s\) intervals gives \((1+o(1))N/(2r\log(N/r))\). Weighted prime partial summation for \(r\) gives \(\int_{1/4}^{7/25}du/(u(1-u))=\log(7/6)\) after extracting the two logarithms. Deleting \(r\mid N\) loses \(o(1)\) in the reciprocal-prime sum. Deleting \(s\mid N\) costs at most \(O(N^{7/25}\log N)\) pairs. Use the lower bound for \(a_m^+\) on the remaining pairs. This proves (15) without a conjecture about prime pairs.

Thus a single already-constructed prime-free sequence can accommodate more than either quantitative supply in (14), even on the intersection with the rough set. On its support \(\lambda=+1\). Track 1's \(H(N)\) sums \(\lambda(m)+(1-\lambda(m))J(m)\) on rough complements, with \(J(m)\) counting their prime divisors in \((N^{2/9},N^{1/3}]\). With the synthetic sequence substituted for the prime weights this is exactly the unsigned rough mass. On the squarefree Chen set the synthetic Möbius bias is exactly the candidate mass. Track 1's fixed automorphic tests still hold for the original sequence. No claim is made that this synthetic example satisfies a two-form progression theorem for actual shifted primes.

In Lü–Wang–Wu's (2.12)–(2.13), every nonzero auxiliary weight requires a prime factor in each of \(K\) disjoint subpower intervals. Besides vanishing on the rough set, it also fails to sample the macroscopic prime witnesses on the Chen set. For \(K\ge3\) the entire Chen set has weight zero. For \(K=2\), a nonzero Chen complement has size at most the product of two subpower endpoints, hence \(N^{o(1)}\). For \(K=1\) and \(m\asymp N\) on the squarefree Chen set, any nonzero weighted term is a semiprime, with Möbius sign **positive**. Its factor in the interval cannot be \(m\) itself. Thus even this last retained part has no mechanism for supplying a negative sign on macroscopic Chen complements. Their fixed-shift theorem and Remark 3 give no target-uniform rough or Chen-restricted estimate at the scale in (14). Granting even an unrestricted reflected \(o(\pi(N))\) would leave this support calculation intact.

## 5. Combining detectors on sparse conductors

For the original GWX weight, Track 2 (6) and (7a) give a useful simplification on \(N=2p^2\). Only \(p,p^2\) have nonprincipal primitive families. On an arbitrarily small fixed line distance for \(p\), its unnormalized contribution to \(G(N)\) is
\[
 O\!\left(\frac{N^{1+2\eta'}}{\varphi(N)}p^{1-2\eta'+\epsilon}\right)
               = O_\epsilon(N^{1/2+\epsilon})
\]
after choosing \(\eta'\) and the auxiliary exponent sufficiently small. The \(p^2\) integral can stay on any one of Track 2's permitted lines. Hence
\[
 \frac{N^{1+2\eta}}{\varphi(N)} I_{p^2}(N;\eta)
       =G(N)-N\mathfrak S(N)+O_\epsilon(N^{1/2+\epsilon}).         \tag{16}
\]
Thus the smaller conductors have already been eliminated to square-root precision for this particular question. This concerns order \(N\) deficits. Detecting a single representation below that remainder would require finer information. Equation (11) gives an exact version at \(2^k\) for a different fixed test, with normalization by \(\varphi^*(N)\). Neither assertion averages a worst-case target away.

**A reflection hole invisible at every lower conductor.** For each \(N=2^k,\ k\ge3\), or \(N=2p^2,\ p\) odd prime, let \(U_N=(\mathbb Z/N\mathbb Z)^\times\). There is a bounded nonnegative \(f\) on \(U_N\) of mean one with all three properties below.

1. \(f(x)f(-x)=0\) at every unit.
2. Every nonprincipal character below the largest primitive conductor has exactly zero coefficient on \(f\).
3. The centered additive Fourier coefficients of \(f-1_{U_N}\), with zero extension to the whole ring, can simultaneously be \(O(\sqrt{N\log N})\). The same bound can simultaneously be enforced on all centered multiplicative character sums.

For \(N=2^k\), partition units into orbits under translation by \(N/2\) and negation. Every orbit has four elements because neither involution fixes a unit and \(2x=N/2\bmod N\) is impossible for odd \(x\) when \(k\ge3\). On an orbit represented by \(x\), select either \(\{x,-x+N/2\}\) or its complement in the orbit, and assign the selected elements weight 2. Each fiber over \(U_{N/2}\) has total weight two and no reflected pair survives. Every proper conductor divides \(N/2\).

For \(N=2p^2\), identify the units with \(U_{p^2}\) by reduction. Fibers over \(U_p\) occur in distinct pairs \(F,-F\), each of size \(p\). In \(F\) omit one lift and partition the rest into pairs \(x,y\). Omit also the negative of the omitted lift. For each pair select \(x,-y\) or \(y,-x\), with weight \(2p/(p-1)\) at both selected points. Each fiber now has total \(p\), reflected support is disjoint, and every character of smaller conductor factors through \(U_p\). This proves the first two assertions. In both constructions choose independently and equiprobably on the four-point blocks. For any given phase function of modulus one, the centered random fluctuation is a sum of \(O(N)\) independent bounded terms. The expectation of \(f-1_{U_N}\) is zero in the first construction. In the second it has total absolute mass \(O(p)\), from the omitted lifts and the \(1/(p-1)\) excess in mean on the others. Hoeffding on real and imaginary parts and a union bound over the \(N+\varphi(N)\) phases prove the last assertion.

By multiplicative Fourier inversion,
\[
   0=\sum_{x\in U_N}f(x)f(-x)
     =\frac1{\varphi(N)}
        \sum_{\chi\bmod N}\chi(-1)
                  \left|\sum_{x\in U_N} f(x)\overline{\chi(x)}\right|^2.
\]
The principal term on the right is \(\varphi(N)\). The top primitive family supplies precisely \(-\varphi(N)\) after normalization. Exact lower-conductor uniformity, nearly square-root centered Fourier coefficients and perfect knowledge of the principal mass are therefore compatible with a full reflection deficit at a *single* conductor. This example tests those three deductions jointly. It does not supply synthetic Euler products satisfying GRH or GWX ratios. Equation (15) tests the different sieve and fixed-automorphic deductions. No amalgamation of the two artificial sequences into a model of all the hypotheses is being assumed.

Finally the original circle coefficient at \(N\) equals \(e^{-1}G(N)\), while (9), (11) and (16) all display \(G(N)\) with known coefficients. A linear combination of identities that cancels the unknown \(G(N)\) cancels the desired signal as well. A positive supply from Chen or (14) changes the available baseline, but its difference from twice the prime count is the still unknown Möbius bias. An extremal weight, a mean over conductors, and an upper-bound sieve can all be valid while their common fixed-target lower bound remains unpaid.

**Verdict.** There is an exact off-diagonal subtraction, a Selberg specialization with explicit surviving frequency terms, an improved narrow almost-prime criterion, and individual-conductor identities and countertests. I have no estimate excluding the critical negative residual for every even \(N\) under the granted RH assumptions. For the original GWX test the missing sufficient estimate is, for example,
\[
 \frac1{\varphi(N)}\sum_{1<q\mid N}N^{2\eta_q}I_q(N;\eta_q)
       \ge -(1-\delta)\mathfrak S(N)
\]
for some fixed \(\delta>0\) and all sufficiently large even \(N\). A positive margin would absorb the independent \(O_\epsilon(N^{1/2+\epsilon})\) remainder in the unnormalized count and its proper-prime-power contribution. An all-even conclusion would also need an explicit bridge to the finite verification through \(4\cdot10^{18}\), or Track 2 (8) at every remaining target. This conclusion concerns the calculations and input theorems above. Logical independence of binary Goldbach from the RH hypotheses is a separate question.

### Local sources

* The previous deductions are in the [pointwise analysis](/home/nisbenz/.t3/projects/weak-goldbach/proof/strong_goldbach_research.md), [Track 1](/home/nisbenz/.t3/projects/weak-goldbach/proof/strong_goldbach_erh_attack.md) and [Track 2](/home/nisbenz/.t3/projects/weak-goldbach/proof/strong_goldbach_nov2026_ratios_attack.md).
* A. Pascadi, *Sums of Kloosterman fractions and applications*, arXiv:2611.34917v1, Theorems 1.1–1.2, Lemma 3.1, (4.11)–(4.13), Corollaries 4.8–4.10 and Theorems 5.1–5.3. [Cached PDF](/tmp/pascadi_2611.pdf)
* H. Gou, V. Y. Wang and M. W. Xu, *Landau's problems through ratios of \(L\)-functions*, arXiv:2611.18825v1, (2.3)–(2.12), Proposition 2.1 and §§3.1–3.6. [Cached PDF](/tmp/gou_wang_xu_2611.pdf)
* J. Li and J. Liu, arXiv:2606.05224v2, (1.3), Theorems 1.1 and 1.3, the definition of WEH, Lemmas 3.1–3.4, §§4–5, 7 and 8.2. [Cached PDF](/tmp/li_liu_19.pdf)
* G. Lü, Z. Wang and J. Wu, arXiv:2610.20242v2, Theorem 1, Remark 3, (2.12)–(2.16) and §5.3. [Cached PDF](/tmp/lu_wang_wu.pdf)

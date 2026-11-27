# B-004 / B-014 · The conductor barrier in the Dirichlet ratios detector

**[I] Verdict.** Retain one analytic blocker, B-004. The differentiated absolute estimate reaches the detector cost exactly. A uniform signed lower bound for genuine Mangoldt correlations at a prescribed even target remains open, including under explicit Dirichlet ERH. The finite tests below distinguish an isolated conductor with an exact weight from the same conductor with the original weight. They also give a fixed smooth positive-semidefinite test whose centered mass attains the entire negative model at four small targets.

[Q] Tags apply to their entire paragraph, display or table. [Q] means read from a local source, [P] means a derivation here or a computation actually run, [I] means interpretation or proposal, and [U] means an unverified external input. The present work has research status. No Lean verdict was issued.

[Q] Denote by **R** the local ratios report and by **D** the persistent-push report. [U] Their external attributions to Gou–Wang–Xu (arXiv:2611.18825v1), Pascadi (arXiv:2611.34917v1), and the Bettin–Chandee estimate quoted there are unverified. Their implications below are conditional on the inputs as transcribed. In particular GWX Hypothesis 1.1 is an additional ratios hypothesis. Dirichlet ERH alone in the local derivations means GRH for the Dirichlet functions used there.

## 1. Three cutoff optimizations

[Q] In R, the undifferentiated ratio uses conjugate characters and normalization by \(q\). Its numerator shifts have real part \(1/2\), its denominator shifts have real part \(1/2+\eta\), and the heights are logarithmic in \(q\). Use \(0<\eta<1/8\) for the ratio budgets, \(0<\eta<1/4\) for the direct differentiated calculation. In the following balances the shifts and the cutoff powers are fixed. Arbitrarily small exponent losses and constants depending on those fixed parameters are understood.

**[P] Separate Möbius cutoffs, R(1)–(3).** For a smooth cutoff equal to one up to one, move its Mellin variable from the absolutely convergent line to \(-\eta+d\), \(0<d<\eta\). The residue at zero is \(1/L\). With the fixed-distance reciprocal bound under ERH as in R, the remainder costs \(q^\epsilon M^{-\eta+d}\). Replacing the two reciprocals has a linear error by expanding the difference of two products. An error of size \(M^{-2\eta}\) would count only the quadratic term.

[P] For a dyadic numerator box \(m\asymp H,n\asymp K\), the approximate functional equation has \(HK\ll q^{1+\epsilon}\). For Möbius indices \(r\asymp U,v\asymp V\), group \(mr,nv\) as two integers, removing the integer diagonal with its exact coefficient. Each nonzero congruence difference or positive sum is divisible only by \(d_0\ll\max(HU,KV)\). Counting the smaller variable first bounds the number of pairs by \(O(HKUV/d_0)\) before divisor multiplicities \(q^\epsilon\). The weights cost \((HKUV)^{-1/2}(UV)^{-\eta}\). Sum \(\varphi(d_0)/d_0\le1\) over the divisors and normalize by \(q\). The result is \(q^{-1/2+\epsilon}(UV)^{1/2-\eta}\), at most \(q^{-1/2+\epsilon}M^{1-2\eta}\) for \(r,v\ll M\). Both congruence signs and composite divisors enter this count.

[P] In the diagonal \(r=g r',v=g v'\), write \(m=v'\ell,n=r'\ell\), with \((r',v')=1\). Apart from the smoothed harmonic \(\ell\)-sum, the majorant is \(g^{-1-2\eta}(r'v')^{-1-\eta}\). Outside a separate cutoff insert \((g\max(r',v')/M)^{\eta-d}\). All three series converge and the truncation costs \(M^{-\eta+d}\). Moving the infinite diagonal's contour to \(-h\) gives a further \(q^{-h}\) from its conductor factor. R identifies the two zero residues with the full model and cancels the two opposite numerator-zeta poles between the direct and reflected pieces [Q, U for the transcribed model]. The strict inequality \(h<\eta\) keeps the denominator zeta factors to the right of one.

[P] At \(M=q^\theta\) the saving envelope is \(\min(\theta\eta,\,1/2-(1-2\eta)\theta,\,h)\). The first function increases and the second decreases, so their crossing is the unique optimum before the \(h\) cap. Solving \(\theta(1-\eta)=1/2\) gives \(\theta=1/[2(1-\eta)]\), saving \(\eta/[2(1-\eta)]\). Choose \(h\) strictly between that saving and \(\eta\).

**[P] Joint Möbius cutoff.** A single Mellin shift in \(V(rv/Y)\) acts on both denominators and gives \(Y^{-\eta+d}\). In the off-diagonal count \(UV\ll Y\) gives \(q^{-1/2}Y^{1/2-\eta}\). In the diagonal insert \((g^2r'v'/Y)^{\eta-d}\) where \(g^2r'v'>Y\). The remaining exponents are \(-1-2d,-1-d,-1-d\). At \(Y=q^\nu\) the two limiting savings are \(\nu\eta\) and \(1/2-\nu(1/2-\eta)\). Their crossing is \(\nu=1\), saving \(\eta\) up to \(\epsilon\), taking \(h\uparrow\eta\) as a function of the desired loss. This optimum concerns a single product cutoff.

**[P] Direct differentiated error, R(7a).** Now sum the two logarithmic derivatives with \(\chi(-1)\) *before* counting. Under the fixed-line log-derivative estimates in R the unnormalized Mellin tail costs \(\varphi^*(q)Y^{-\eta+d}\) times logarithms. In the retained polynomial the unit-pair coefficient is
\[
 b_q(m+n)=\sum_{d_0\mid(q,m+n)}\mu(q/d_0)\varphi(d_0).
\]
Since \(m+n>0\), a divisor contributing to a box \(H,K\) has \(d_0\ll\max(H,K)\). Counting \(O(HK/d_0)\) pairs, applying the two Mangoldt upper bounds and summing divisors gives \(Y^{1/2-\eta}q^\epsilon\). Thus the normalized savings are \(\nu\eta\) and \(1-\nu(1/2-\eta)\). They cross at \(\nu=2\) with saving \(2\eta\). The transcribed model has a bounded parity-imbalance term and a family-size term times \(q^{-2\eta}\) from the two gamma factors [Q, U]. The absolute kernel is integrable with the required height weights [Q, U]. Together these give an **unnormalized** envelope \(q^{1-2\eta+\epsilon}\) for \(B_q=\iint|K E_q|/(2\pi)^2\), \(E_q=A_q-H_q\). At \(q\asymp N\) the detector multiplies by \(N^{2\eta}/\varphi(N)\) in its normalized error. This power pays precisely for that multiplier. The equality concerns an upper-bound method and supplies no lower bound for the true error.

**[P] Bettin–Chandee repair, D §2, conditional on the quoted norm [U].** Take prime \(q\), coprime inverse variables \(r,v\asymp M\), \(q^{1/2}\le M<q/3\), and numerator lengths \(\asymp\sqrt q\). After Poisson, two nonzero outer variables have size \(M/\sqrt q\); grouping their product gives \(A\asymp M^2/q\). The multiplier is \(q\). Consequently \((1+qA/M^2)^{1/2}=O(1)\). The given norm is \(M^{19/20}A^{7/20}+M^{7/8}A^{1/2}\). Multiply by \(M\sqrt A\,M^{o(1)}\) from the three coefficient norms and by \(M^{-2-2\eta}\) from scaling. The cost becomes
\[
 M^{-2\eta+o(1)}(M^{-1/20}A^{17/20}+M^{-1/8}A)
 =q^{o(1)}(q^{-17/20}M^{33/20-2\eta}+q^{-1}M^{15/8-2\eta})
\]
at the level of powers. Both terms save a power for
\[
 \tfrac12\le\theta<\min\{17/(33-40\eta),\,8/(15-16\eta)\}.
\]
At zero damping the limiting upper bound is \(17/33\). For \(0<\eta<1/8\) the first upper bound is at most \(17/28<0.608\). By comparison, individual reciprocal substitution at this accuracy needs \(\theta\eta>2\eta\), hence \(\theta>2\). A joint tail of size \(Y^{-\eta}\) needs a fixed power \(Y=q^{2+\kappa}\), \(\kappa>0\), for a power improvement. A constant multiple of \(q^2\) gives the same exponent. The available balanced-block gain concerns the error around the Poisson zero frequency. A full estimate still needs that frequency and the principal subtraction, both parity projectors, unbalanced blocks, composite moduli and the tails. The zeta height exponent quoted for Pascadi is external [U].

## 2. Exact arithmetic and interval calculations

[Q] D(2) is the arithmetic subtraction for a test \(W\). With \(F_+(h)=\int_0^h W(u,h-u)\,du\) and \(F_-(h)=\int_0^\infty(W(u+h,u)+W(u,u+h))\,du\), it reads
\[
 [E_q,W]=\sum_h b_q(h)(G_{q,W}(h)-\mathfrak S(h)F_+(h))
 -\Delta\sum_{(j,q)=1}\Lambda(j)^2W(j,j)-\Delta\sum_h k_q(h)F_-(h).
\]
Here \(G_{q,W}\) counts ordered unit pairs; \(\Delta=b_q(2)\). Its analytic identification uses the local ERH contour argument and the transcribed GWX model [U]. Arithmetically, the character projector on units gives \(b_q(m+n)\). Divisor inversion of the proposed model projection gives \(\varphi^*(q)k_q(h)=b_q(h)\mathfrak S(h)\) without division by either local quantity [P, conditional on that projection]. For all top conductors used below, \(\Delta=0\).

[P] At \(N=q=2^k\), only \(d=q,q/2\) contribute to \(b_q(h)\). Its coefficient at \(h=N\) is \(\varphi^*(q)=2^{k-2}\). In the D(11) weight \(w_2\), the zero set includes every other positive half-integer \(h/N\) on which \(b_q\) can be nonzero. For \(N=2p^2,\ q=p^2\), \(b_q(h)=p(p-1)1_{p^2\mid h}-(p-1)1_{p\mid h}\), \(b_q(N)=(p-1)^2\). The variable weight \(w_{2p}\) kills the other multiples of \(p\). In both cases the sole deleted ordered pair of positive Mangoldt weight at the target is \((N/2,N/2)\). For the dyadic case, two unequal powers of two cannot add to a power of two. For the odd-prime case, if \(p^a+p^b=2p^2\) and \(a<b\), valuation forces \(a=2\) and \(1+p^{b-2}=2\), impossible. Equal exponents give \((p^2,p^2)\). The deleted weight for this second family is **\((\log p)^2\)**.

[P] Write \(C_2=\prod_{\ell>2}(1-(\ell-1)^{-2})\). The exact symbolic data for each target are the integer multiplicities of \(\log a\log b\) for unordered prime bases \(a,b\), counting ordered pairs of prime powers; the rational coefficient of \(C_2\) in \(N\mathfrak S(N)\); and the base of the deleted log-square. The coefficient is \(2N\) for the dyadics and \(2N(p-1)/(p-2)\) for \(2p^2\). The two sides of the arithmetic deletion were enumerated independently and compared as integers. The full sum was also enclosed by squaring integer polynomials with coefficients obtained by rounding \(10^{14}\Lambda(n)\) down and up before convolution.

[P] Numerical enclosures use Arb at 160 bits. To bound \(C_2\), factor out \(\prod_{\ell>2}(1-\ell^{-2})=4/(3\zeta(2))\). The omitted corrected factors for primes \(\ell>L=10^6\) are \(1-(2\ell-1)/((\ell-1)^2(\ell^2-1))\), with deficit at most \(4/\ell^3\). Their product lies in \([1-2/L^2,1]\) by comparison with the integer tail integral. This gives \(C_2=0.6601618158463\) within \(7.1\cdot10^{-13}\). At eight \(G_{\rm unit}(8)=2\log3\log5=3.536296536897\) within \(10^{-12}\), below 8, and \(\mathfrak S(8)=2C_2>1\). The exact-weight normalized integral in D(11), **including its displayed factor \(N^{1+2\eta}/\varphi^*(N)\)**, is consequently \(-7.026292516643\) within \(1.1\cdot10^{-11}\) under that analytic identity. The finite arithmetic sign requires no ERH.

[P] The relative residual below uses the full \(G\), including proper powers, and is \((G-N\mathfrak S)/(N\mathfrak S)\). Entries are rounded.

| Family | Sample size | Negative / positive | Minimum | Maximum | Last target |
|---|---:|---:|---:|---:|---:|
| \(2^k,\ 3\le k\le16\) | 14 | 8 / 6 | −0.619719 at 8 | +0.120903 at 64 | +0.008189 at 65536 |
| \(2p^2,\ 3\le p\le101\) prime | 25 | 16 / 9 | −0.584355 at 18 | +0.092711 at 1922 | +0.024931 at 20402 |

[P] For example the dyadic residual moves from \(+0.030906\) at 1024 to \(-0.107274\) at 2048. The prime-square family moves from \(-0.094795\) at 1682 to \(+0.092711\) at 1922. Both samples change sign. [I] Their endpoints establish no limiting rate or uniform margin.

**[P] Independent arithmetic evaluation for D(16).** For the *original fixed* \(w=w_1\), the terms \(h=jp\) away from \(N\) generally survive at \(q=p^2\). The quantity identified with the scaled top integral under D(2) is
\[
 L_p=\frac1{p(p-1)}\sum_{p\mid h} b_{p^2}(h) w(h/N)
      \{G_{p^2,1}(h)-h\mathfrak S(h)\}.
\]
Here \(G_{p^2,1}\) means unit restriction with constant weight one. This normalization is by \(\varphi(N)=p(p-1)\). For each \(p\mid h\) remove all ordered \(p^i+p^j=h\) exactly from the integer-convolution enclosure. The singular series is zero for odd \(h\). For the sum through \(5N\) group the model's common factor \(C_2\) before interval multiplication. Beyond \(5N\), \(|b|/\varphi(N)\le1,\ |w(h/N)|\le e^{-20(h/N-1)}\), \(G(h)\le h\log^2 h\le h^2\) and \(\mathfrak S(h)\le2h\) by its Euler factors. Splitting into intervals of length \(N\) bounds the absolute tail by \(216N^3e^{-80}\), since \(\sum_{j\ge0}(6+j)^2 e^{-20j}<72\). All 25 values of \(L_p\) were enclosed by this procedure.

[P] At \(p=3\), \(L_p=557341.681912\) within \(0.000001\), whereas \(G(18)-18\mathfrak S(18)=-27.775365\) to six decimals. At \(p=101\), \(L_p=-2956491.4044\) within \(0.0011\), while \(G(20402)-20402\mathfrak S(20402)=678.364558\) to six decimals. The original exponential weight amplifies small positive \(h/N\). For example \(w_1(1/2)=4e^{10}/\pi^2\). D(16) does **not** assert exact equality at either target. Its stated error follows from R(6) and R(7a) on the lower primitive conductor \(p\) [Q, U for the analytic inputs]. Indeed \(N^{1+2\eta'}/\varphi(N)\cdot p^{1-2\eta'+\epsilon'}\ll p^{1+2\eta'+\epsilon'}\), hence \(O_\epsilon(N^{1/2+\epsilon})\) on choosing the fixed \(\eta',\epsilon'\) sufficiently small. The remaining primitive conductor is \(p^2\). [I] Independently evaluating \(L_p\) and the discrepancy tests the arithmetic terms and their normalizations. With an unspecified implied constant and asymptotic onset, finite comparisons cannot certify or refute the growth estimate. Neither the numerical work nor this audit directly evaluates the double contour integrals.

**[P] PSD test.** Choose the fixed symmetric smooth profiles \(f_a(x)=\exp[-t^2/(1-t^2)]\) for \(t=|x-1/2|/a<1\), extended by zero, with \(a=1/20,1/5\). Their supports are compactly inside \((1/4,3/4)\); the first is also inside \((7/16,9/16)\). For \(W=f_a(u/N)f_a(v/N)\), positivity of the kernel follows from its rank-one factorization. Only \(h=N\) survives the dyadic primitive projector, and \([E_N,W]/\varphi^*(N)\) is the weighted unit-pair mass minus \(N\mathfrak S(N)\int f_a^2\) under D(2). The half-profile square is decreasing. Right and left sums on \(2^{15}\) equal subintervals bound its integral, with exact gap \(2^{-15}\) before multiplying by \(2a\).

[P] The narrow profile has exactly zero actual mass at \(N=8,16,32,64\), with positive model in each case. At eight the only possible integer sample is the nonunit 4. For the same fixed profile, actual/model minus one is \(+1.36875\pm0.00008\) at 128 and \(+0.07879\pm0.00004\) at 65536. The wider profile gives \(-0.52768\pm0.00002\) at 8 and \(-0.00505\pm0.00004\) at 65536. Exact nonnegativity of the actual integrated mass permits the full centered deficit at finite targets.

## 3. Four possible ways past the barrier

**[P] Asymmetric shifts.** Put \(a=\eta_s,\ b=\eta_t\) with \(0<a,b<1/4\). Shifting the two holomorphic contours separately preserves \(N^{1+a+b}I_q(N;a,b)\) under the contour hypotheses in R. The normalized multiplier is \(N^{a+b}/\varphi(N)\), so at a top conductor of size \(N\) an absolute power gain would have to beat \(q^{1-a-b}\). In the naive common-shift proof the tail can move only to \(-\min(a,b)+d\). The box count is \(H^{1/2-a}K^{1/2-b}\), bounded for \(HK\ll Y\) by \(O(Y^{1/2-\min(a,b)})\). Balancing this coarser bound still gives \(Y=q^2\), guaranteeing only the saving \(2\min(a,b)\le a+b\). Resolving unbalanced boxes better leaves \(H,K\asymp q\), \(H^{1/2-a}K^{1/2-b}\asymp q^{1-a-b}\). Under the transcribed model its separate parity gamma terms at zero height likewise have scale \(q^{-a-b}\) per character. Their leading even–odd trigonometric difference is proportional to \(-\cos(\pi(s+t)/2)=\sin(\pi(a+b)/2)\ne0\) there. On the dyadic isolated test the stronger statement \(I_N^{w_2}(N;a,b)=o(N^{1-a-b})\) is exactly \(G_{\rm unit}(N)-N\mathfrak S(N)=o(N)\) by contour invariance and \(\varphi^*(N)=N/4\). Redistributing the shifts gives no improvement in that signed observable. This reasoning leaves open the possibility of new cancellation inside a balanced box.

**[P] Combining conductors.** Möbius inversion gives \(\sum_{q\mid N}b_q(h)=\varphi(N)1_{N\mid h}\) by exchanging the two divisor sums. The inner sum is \(\sum_{e\mid N/d}\mu(e)\). At \(h=N\) this yields \(\sum_{q\mid N}\varphi^*(q)=\varphi(N)\), with the principal conductor included. At \(N=2^k\) the normalized masses of \(2^j\), \(2\le j\le k\), are \(2^{j-k-1}\). The largest carries one half and the largest \(r\le k-1\) carry \(1-2^{-r}\). At \(N=2p^2\) the top carries \(1-1/p\). These are weights in a signed sum. They give no independence or comparison of signs. For a concrete dyadic obstruction partition units into four-point orbits under negation and translation by \(N/2\). Assign weight 2 to \(x,-x+N/2\) in each orbit and zero to their partners. Each lower fiber has its usual total mass, so every nonprincipal character factoring through \(N/2\) has zero coefficient. The reflected supports are disjoint. Character orthogonality therefore places the full negative principal contribution at the top conductor. The test is for abstract nonnegative weights. Supplying the Euler-product and Mangoldt structure would be a separate argument.

[P] On the moving line, split at \(q=\sqrt N\). For smaller \(q\) return to a fixed \(\eta_0<1/8\); the bound \(B_q(\eta_0)\ll q^{1+\epsilon}\) quoted under ERH gives \(O(N^{-1/2+2\eta_0+O(\epsilon)})\) in the normalized total by the divisor bound. Above the split \(N^{2c/\log(2q)}\le e^{4c}\), so the exact conductor-mass identity makes a uniform \(B_q(c/\log(2q))/\varphi^*(q)\to0\) sufficient. A dyadic average in \(q\) allows an exceptional top conductor. At the fixed-power cutoff \(Y=q^\nu\), the formal tail factor is \(e^{-\nu c+o(1)}\), and fixed-\(\eta\) constants supply no limiting estimate. [I] An independent estimate for the weighted signed sum could allow cancellation, but neither the mass identity nor the computations supply it.

**[P] Projection before truncation.** With all induced characters modulo \(N\), including the principal character, the complete projector imposes \(N\mid m+n\) on units. With \(w_1((m+n)/N)\) only \(m+n=N\) remains. On that line \(4mn\le N^2\), so a common cutoff equal to one up to \(Y=N^2/4\) changes the actual projected count by exactly zero. This cancellation uses the actual coefficients *after summing all conductors*. Before projection, common-shift smoothing of \(E\) using the critical bound on the line at distance \(d\) has tail \(q^{1-2d+\epsilon}Y^{d-\eta}\). At \(Y=q^2\) this is \(q^{1-2\eta+\epsilon}\) for every \(d\). Merely iterating that estimate cannot improve its exponent.

[P] After projection the missing quantity on any fixed interior interval \(D\subset(0,1)\) is a shifted convolution
\[
 \sum_{\substack{m/N\in D\\(m(N-m),N)=1}}\Lambda(m)\Lambda(N-m)
       -N\,|D|\,\mathfrak S(N)
\]
or its smooth version. A deficit of size \(N\) at \(q\asymp N\) in a balanced box with \(|b_q(N)|\asymp q\) costs \(q\,N^{-1-a-b}N\asymp q^{1-a-b}\) after the two Dirichlet weights. A dispersion estimate summing squared residuals over shifts permits a single deficit \(cN\) whenever the total budget permits \(c^2N^2\). Passing to a single target by positivity requires a sufficiently small total budget or further localization with control of that target. A fixed-shift spectral estimate would need the main term, the actual coefficients on \(m+(N-m)=N\), and an error or one-sided constant small enough at each prescribed \(N\). The balanced determinant estimates in §1 concern different variables and a Poisson frequency average. [I] Removing the projected tail is exact progress on truncation, but leaves this single-shift lower bound in full.

**[P] One-sided minorants.** For \(b\ge1\) put \(w_b(v)=(2-v)e^{-b(v-1)}\), \(D(h)=G(h)-h\mathfrak S(h)\), and \(D_b(N)=\sum_{k\ge1}w_b(k)D(kN)\). The actual projected sum minorizes \(G(N)\). The fractional loss in its model is at most \(\sum_{k\ge3}k(k-2)\tau(k)e^{-b(k-1)}=O(e^{-2b})\), since \(\mathfrak S(kN)/\mathfrak S(N)\le\tau(k)\). One can quantify how closely this test reproduces the original discrepancy even without ERH:
\[
 \frac{|D_b(N)-D(N)|}{N\mathfrak S(N)}
       \ll e^{-2b}\log^2(2N)\qquad (b\ge1,\ N\text{ even}).
\]
Indeed \(G(kN)\le kN\log^2(kN)\), \(\mathfrak S(N)\ge 2C_2>1\), and \(\log(kN)\le(1+\log k)\log(2N)\). Factor \(e^{-2b}\) out of the terms with \(k\ge3\); the remaining exponential series in \(k\), with the divisor and logarithmic factors, converges uniformly for \(b\ge1\). Thus even \(b=(1+\epsilon)\log\log(2N)\) makes the normalized difference \(o(1)\). This is only an approximation to the same unknown discrepancy; a varying \(b\) would also require its own uniform analytic bounds.

[P] There is a one-sided obstruction uniform in the *other* coefficients even at fixed \(b\). If an even \(N\) has no prime representation, \(G(N)\ll\sqrt N\log^{O(1)}N\) by counting proper powers. Since each \(w_b(k)\le0\) for \(k\ge2\) and \(G(kN)\ge0\), we would have \(D_b(N)/(N\mathfrak S(N))\le-1+O(e^{-2b})+o(1)\) along such a sequence. The test's rank at most two and its small model loss give no lower bound excluding that value. An independent estimate for \(D_b\) or the phase-weighted error is still required.

**[Q, P] Finite endpoint and scope.** R(6) gives \(G(N)=N(\mathfrak S(N)+J(N))+O_\epsilon(N^{1/2+\epsilon})\) under its analytic assumptions. A fixed \(\delta>0\) and \(J(N)\ge-(1-\delta)\mathfrak S(N)\) leave a positive margin exceeding both the independent remainder and the proper-power mass for sufficiently large even \(N\). For an exact endpoint, use the induced-character observable of R(8), with the principal integral and model retained in the explicit baseline \(\mathcal B(N)\). The sufficient strict inequality is
\[
 \frac{N}{\varphi(N)}\sum_{1<q\mid N}N^{2\eta_q}I^{\rm ind}_{q,N}(N;\eta_q)
 >2(\psi(N)-\vartheta(N))\log N-\mathcal B(N).
\]
The upper bound counts each choice of a proper-power coordinate with its other coordinate weighted by at most \(\log N\). Targets with \(N/2\) prime have the diagonal prime representation. [U] The cited finite verification through \(4\cdot10^{18}\) is external to the local kernel-checked range. [I] A qualitative sufficiently-large estimate would still leave its onset to bridge. None of the four tests establishes R(7), R(8), or a fixed positive one-sided margin.

## 4. Proposed Lean micro-lemma and issue disposition

[I] **PROPOSED** exact dyadic primitive-projector identity. With mathlib's integer Möbius function and natural totient, the prospective statement is the proposition below. A build should pin the imports and confirm the identifiers. It has no analytic hypotheses, includes \(h=0\), and avoids truncated natural subtraction by doing the arithmetic in \(\mathbb Z\).

~~~lean
def B004DyadicProjectorStatement : Prop :=
  ∀ k h : ℕ, 2 ≤ k →
    (∑ d ∈ (Nat.gcd (2 ^ k) h).divisors,
      ArithmeticFunction.moebius ((2 ^ k) / d) * (Nat.totient d : ℤ)) =
      (if 2 ^ k ∣ h then (Nat.totient (2 ^ k) : ℤ) else 0) -
      (if 2 ^ (k - 1) ∣ h then (Nat.totient (2 ^ (k - 1)) : ℤ) else 0)
~~~

[P] Every divisor \(d\mid 2^k\) is \(2^j\), \(0\le j\le k\). The quotient has Möbius value zero for \(j\le k-2\), minus one for \(j=k-1\), and one for \(j=k\). Intersect these two surviving divisors with \(d\mid h\). This proves the displayed mathematical identity and gives the reading of the \(h=0\) branch. [I] The Lean declaration is a proposed specification only. No theorem was submitted or promoted.

[I] Use B-004 (#4) for the single open analytic estimate. Keep B-014 (#11) as a cross-reference with a specific source-verification task if the owner wants to track GWX Hypothesis 1.1 and the Pascadi parameter ranges separately. Both currently ask for the same conductor saving or one-sided replacement; the finite examples resolve neither. A useful new analytic input would estimate the **subtracted** actual/model moment on the balanced single shift or prove the induced finite-endpoint inequality uniformly, with its signed constant.

## Evidence and reproduction

[Q] Local sources. [R §§2–7](/home/nisbenz/.t3/projects/weak-goldbach/proof/strong_goldbach_nov2026_ratios_attack.md) · [D §§1–3 and §5](/home/nisbenz/.t3/projects/weak-goldbach/proof/strong_goldbach_persistent_push.md) · [Audit C27](/home/nisbenz/.t3/projects/weak-goldbach/attack/audit/REPO_AUDIT.md:85)

[P] Reproduce with Python and python-flint 0.9.0. The script locates its output directory relative to itself. The integer tables and interval calculations are unconditional arithmetic. Local outputs in /tmp are temporary. The analytic link to the integrals has the assumptions stated above.

~~~sh
uv venv --python /usr/bin/python3 /tmp/astra_b004/venv
uv pip install --python /tmp/astra_b004/venv/bin/python python-flint==0.9.0
/tmp/astra_b004/venv/bin/python /tmp/astra_b004/verify.py
~~~

[P] Run output and files. 39 targets, 25 original-weight projections, 28 PSD cases; all program assertions passed. [Verification script](/tmp/astra_b004/verify.py) · [Exact symbolic coefficients](/tmp/astra_b004/symbolic.json) · [Isolated weights](/tmp/astra_b004/isolated.tsv) · [Original-weight equation (16)](/tmp/astra_b004/original16.tsv) · [PSD profiles](/tmp/astra_b004/profiles.tsv) · [Relative residual plot](/tmp/astra_b004/residuals.png)

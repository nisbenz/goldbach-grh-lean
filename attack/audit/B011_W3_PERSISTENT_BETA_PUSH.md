# Which zero heights matter at a fixed Goldbach target?

[Q] Wave 3, 27 November 2026, astra-w3-b011. Throughout the zero estimates assume Dirichlet ERH, including RH for zeta. Tags denote sourced inputs [Q], derivations or finite computations [P], interpretations [I], and unresolved estimates [U]. The estimates below are mathematical derivations with unspecified absolute constants. They have no Lean checker verdict.

[P] Two estimates improve the Wave 2 bounds. With natural zero weights, the full-line positive block is \(O(N\log N)\) for \(T\asymp N\) and polynomially bounded conductors. On the actual circle, in a Farey dissection of order \(Q\asymp\sqrt N\), the entire field from ordinates \(|\gamma|\ge Y=(\log N)^4\) can be removed at cost \(O(N/\sqrt{\log N})\) in the signed coefficient, including its interactions with every other term. This holds on either H1/H2 complement. [U] The sign of the residual coefficient is open.

## 1. The full-line beta integral differentiates both errors

[P] For finite multisets of zeros \(A,B\), let \(P_A(t)=-\sum_{\rho\in A}t^\rho/\rho\). Termwise Euler integration gives the exact identity
\[
 e^{-1}\sum_{A,B}N^{\rho+\rho'-1} B(\rho,\rho')
   = e^{-1}\int_0^N P_A'(t)P_B'(N-t)\,dt.                 \tag{1}
\]
Indeed \(-P_A'(t)=t^{-1/2}\sum_A e^{i\gamma\log t}\). The factors \(1/\rho\) from the prime-counting explicit formula have disappeared on **both** sides of the convolution. For zeta the distributional prime error is \(d\psi-dt\). Its additive self-convolution on the positive half-line has atoms \(\sum_{j+k=n}\Lambda(j)\Lambda(k)\,\delta_n\), and continuous part \((t-2\psi(t))dt\). This follows by multiplying out the two measures. Projecting to nontrivial zeros requires retaining the trivial-zero corrections, and projecting to positive heights is a further restriction. A full unsmoothed zero sum cannot be evaluated termwise at an integer on the basis of (1).

[P] On a fixed interior interval in \(x=t/N\), the Wave 2 local mean-value bound for a single block with the **primitive** weights \(1/\rho\) gives an \(L^2(dx)\) norm \(\ll\sqrt N\log(2dT)/\sqrt T\) for \(P_A(Nx)\). The dyadic norms sum to \(O(\sqrt N\log(2d))\), including the bounded-height zeros by the unit-interval count. For zeta the elementary terms of the explicit formula are bounded away from \(t=1\), so this also gives \(\int_0^1|\psi(Nx)-Nx|^2 dx\ll N\) by subdividing into geometrically decreasing spatial intervals (handle \(t\le 2\) directly). These mean squares concern the primitive. On differentiating a height block, the relative cost in the normalized oscillatory sum is of order \(T\) per input.

### A logarithm saved for the natural weights

[P] Put \(I=[T,2T)\), \(T\ge2\), and choose a fixed smooth compactly supported \(\eta(s)\) equal to one on \(\log([1/4,3/4])\), with \(e^s\) in a fixed compact subinterval of \((0,1)\) on its support. For large \(N\), set
\[
 f_I(s)=\eta(s)\sum_{\gamma\in I}e^{i\gamma(\log N+s)},\quad
 L_d=\log(2dT).
\]
Then
\[
 \|f_I\|_2^2\ll \min\{T L_d^2,\ (T+N)\log(2N)+L_d^2\}.     \tag{2}
\]
The first branch is Wave 2. Here is a proof of the second for a primitive character \(\chi\) of conductor \(d\).

1. [P] Localize the **all-ordinate** distribution by the same \(\eta\), and project it in Fourier space to \(I\) (frequency convention \(e^{i\xi s}\)). This differs from \(f_I\) in \(L^2\) by \(O(L_d)\). Indeed its Fourier error is a sum of translates \(N^{i\gamma}\widehat\eta(\xi-\gamma)\) with the two frequencies on opposite sides of a band edge. Group ordinates into unit bins by distance to that edge. A bin at distance \(j\) contains \(O(L_d+\log(2+j))\) zeros. For any fixed \(k\), Schwartz decay bounds the sum across either edge \(b\) by \(O_k(L_d(1+|\xi-b|)^{-k})\). This also treats repeated zeros exactly at an endpoint.
2. [P] On \(v=\log N+s>0\), the differentiated explicit formula for a primitive character reads, as distributions,
   \[
   \sum_\gamma e^{i\gamma v}
     =\mathbf1_{d=1}e^{v/2}
      -\sum_n \chi(n)\Lambda(n)n^{-1/2}\delta_{\log n}(v)
      -\sum_{-k\ {\rm trivial}}e^{-(k+1/2)v}.
   \]
   One derivation tests against a smooth function supported in \(v>0\), applies Mellin inversion to \(-L'/L\), and takes residues at the pole and the nontrivial and trivial zeros. Equivalently differentiate the integrated explicit formula there. Constants supported at \(v=0\) vanish. The trivial zeros form a parity progression, with the conductor-one case starting at \(-2\). After multiplication by \(\eta\), the smooth terms have squared Fourier mass on \(I\) of \(O_k(NT^{-k})\) by integration by parts.
3. [P] The remaining frequencies in the Fourier transform are \(\log(n/N)\), for \(n\asymp N\), separated by \(\gg 1/N\). Their coefficients \(c_n=\eta(\log(n/N))\chi(n)\Lambda(n)/\sqrt n\) satisfy \(\sum|c_n|^2\ll\log(2N)\) by Chebyshev's bound. Majorize \(I\) by a smooth bump of width \(O(T)\). The absolute row sums of its Fourier kernel are \(\ll T\sum_{j\ge0}(1+Tj/N)^{-2}\ll T+N\). The quadratic form is therefore \(\ll (T+N)\sum|c_n|^2\). Plancherel and step 1 give (2).

[P] On the central beta integral use Cauchy–Schwarz and (2) for each input. The exterior costs \(O(L_d L_{d'})\) by the two nonstationary integrations in Wave 2. Thus for \(T\asymp N\) and \(d,d'\le N^A\) for fixed \(A\), the full block is \(O_A(N\log N)\). The phase \(N^{i\gamma}\) and the genuine unit weights are essential in step 2. For \(2\le T\le Y\) dyadic, Wave 2 already sums the comparable-height diagonal blocks to \(O(Y\log(2dY)\log(2d'Y))\) by geometric growth. Neither that estimate nor (2) gives a decaying full-line tail to infinity.

[P] There is a one-field logarithmic floor for this Cauchy–Schwarz method. Take zeta and \(T=KN\) for a sufficiently large fixed \(K\). Test the prime polynomial in step 3 with a nonnegative smooth bump *inside* \(I\) of bounded height and mass \(cT\). The off-diagonal absolute row sums are \(O(T/K^2)\) by the same spacing, now excluding \(j=0\). Hence the squared integral is \(\gg T\sum|c_n|^2\gg T\log N\) by the prime number theorem on an interior subinterval where \(\eta=1\). The smooth terms and the \(O(\log T)\) norm at the band edges are negligible. This proves sharp order in (2) there, without asserting a lower bound for the signed two-input block.

[P] For a common full-line kernel at \(q\mid N\), summing centers pairs only \(\chi' = \bar\chi\). With coefficients \(c_\chi=\tau(\bar\chi)/\varphi(q)\), the absolute coefficient cost is exactly \(\varphi(q)\sum_\chi|c_\chi|^2=\varphi(q)\), since conjugate Gauss sums have equal magnitude. The cumulative divisor cost for \(q\le H\) is at most \(\min(N,H\tau(N))\), by \(\sum_{q\mid N}\varphi(q)=N\). For all \(q\le H\) the central beta integral costs at most \(\sum\varphi(q)\ll H^2\) times the worst one-field squared norm, by character orthogonality at each \(x\) and Cauchy–Schwarz across centers and \(x\). This gives a central allowance of order \(H^2 N\log N\) at the critical height. The actual cells have different integration windows. Their bound follows next.

## 2. A summable height tail on the H1/H2 complement

[P] Fix \(Q=\lfloor\sqrt{2\pi N}\rfloor\). Assign each point of the circle measurably to one reduced Dirichlet approximation \(a/q\), \(q\le Q,\ |\beta|=|\alpha-a/q|\le1/(qQ)\), breaking ties arbitrarily. Intersect these cells with any measurable \(B\), in particular \(\mathbb T\setminus A_y\). Define \(Z_T\) on each cell to be the positive-ordinate piece of the primitive zero term for \(T\le\gamma<2T\), including its character coefficients. For \(T\ge 2\),
\[
 \|\mathbf1_B Z_T\|_2^2
   \ll {N\over T}\log^2(2QT)\exp(-cTQ/N).                 \tag{3}
\]
The negative band obeys the same estimate. The cell assignment is part of the definition of this field.

[P] **One shell.** Put \(u=2\pi N\beta\) and \(z=(1-iu)/N\). On either shell \(V\le |u|\le2V\), \(V\ge1\), a single primitive field \(Z_{\chi,T}=\sum_{\gamma\in I}\Gamma(1/2+i\gamma)z^{-1/2-i\gamma}\) satisfies
\[
 \int_{\rm shell}|Z_{\chi,T}|^2d\beta
      \ll T\log^2(2dT)e^{-cT/V}.                           \tag{4}
\]
To see this, remove the common \(z^{-1/2}\), absorb \(N^{i\gamma}\Gamma(1/2+i\gamma)e^{\pi\gamma/2}\) as a bounded coefficient, and use \(s=\tfrac12\log(1+u^2)\). The remaining factor is \(e^{-i\gamma s}e^{-\gamma(\pi/2+\arctan u)}\). The Jacobian \(du/\sqrt{1+u^2}\) in the squared integral is comparable to \(ds\); the interval has bounded length. Use a smooth majorant on the slightly wider shell \(V/2\le|u|\le3V\). There the angle is \(\gg1/V\) and its first two \(s\)-derivatives are \(O(1/V)\). Twice integrating by parts in the expanded square gives a kernel \(\ll e^{-cT/V}(1+|\gamma-\gamma'|)^{-2}\), absorbing polynomial factors in \(T/V\) into the exponential. The unit-interval zero count proves (4). For \(|u|\le1\) direct exponential decay gives the same bound with \(V=1\).

[P] **Centers and conductors.** At fixed \(q,\beta\), enlarge all center-dependent subsets to the common shell in this nonnegative energy bound. On that common domain,
\[
 \sum_a^*\Big|\sum_\chi c_\chi\chi(a) Z_{\chi^*,T}\Big|^2
   =\varphi(q)\sum_\chi |c_\chi|^2 |Z_{\chi^*,T}|^2,\qquad
 \sum_\chi |c_\chi|^2=1.
\]
The second identity is finite Parseval for \(e(b/q)\) on the units, including imprimitive characters. For \(q\asymp R\) the shell thus spends \(O(R^2T\log^2(2QT)e^{-cT/V})\), and only \(q\le 2\pi N/(QV)\) occur. The exact power cost from counting centers up to that cutoff is its square. Summing all such centers gives \(O(N/V^2)\) since \(Q\asymp\sqrt N\). The central shell costs \(O(Q^2)\) centers. Finally
\[
 NT\sum_{1\le V\ll N/Q\ {\rm dyadic}} V^{-2}e^{-cT/V}
 \ll (N/T)e^{-c'TQ/N}
\]
by setting \(v=T/V\) and summing \(v^2e^{-cv/2}\). This proves (3). No cancellation in a twisted sum at an individual center or between different denominators was assumed.

[P] **Exponent ledger.** Ignoring logarithms, a shell \(V\asymp T\) has at most \(N/T^2\) centers and spends \(T\) per center in the squared energy. At \(T=N^\theta\), \(0\le\theta\le1/2\), this gives \(N^{1-\theta}\); higher than \(\sqrt N\) the exponential cutoff takes over. In particular the conductor count still permits order \(N\) at bounded height. The \(\varphi(q)\) in the orthogonality identity is exact even when \(q\mid N\). Unequal Farey windows would invalidate using the same *signed* Gauss sum at every center. Enlargement here uses positivity only for the auxiliary squared norm.

[P] **All interactions.** Let \(Z_{\ge Y}\) include the sign used in the explicit formula and both ordinate signs above \(Y\ge2\). Dyadic Minkowski in (3) gives \(\|Z_{\ge Y}\|_2\ll\sqrt{N/Y}\log(2QY)\) on the circle, also for non-dyadic \(Y\) by starting the blocks at \(Y\). The primitive series converges absolutely on every cell at fixed \(N\). Set \(S_{<Y}=S-Z_{\ge Y}\), retaining the pole, residues, imprimitive corrections, and low zeros. The companion Parseval bound \(\|S\|_2^2\ll N\log N\) and the identity \(S^2-S_{<Y}^2=2SZ_{\ge Y}-Z_{\ge Y}^2\) yield, uniformly in \(B\),
\[
 \left|\int_B (S^2-S_{<Y}^2)e(-N\alpha)d\alpha\right|
 \ll N\left({\sqrt{\log N}\log(2QY)\over\sqrt Y}
               +{\log^2(2QY)\over Y}\right).               \tag{5}
\]
For \(Y=(\log N)^4\) this is \(O(N/\sqrt{\log N})\). [U] One still needs a signed estimate for \(S_{<Y}^2\) on the chosen complement with room for (5). The constants here do not give the repository's H1/H2 margins down to its finite endpoint.

## 3. The actual companion model rules out the global norm repair

[Q] Use \(D=S-M,\ G=S+M\) for the companion exceptional-set dissection, with model cutoff \(H=\lfloor Q/2\rfloor\). These are its own arcs. [Companion Lemma 1](../../proof/binary_goldbach_exceptional_proof.md)

[P] Hausdorff–Young and Hölder spend \(\|D\|_r\|G\|_2\) on the \(\ell^p\) norm of the error coefficients, \(r=2p/(p-2)\). With the existing \(\|G\|_2\ll\sqrt{N\log N}\), this deduction needs a power below \(1/2\) for \(\|D\|_r\) to give \(\beta(p)/p<1\). For an \(o(N)\) bound with no fixed power saving the sufficient scale is \(o(\sqrt{N/\log N})\). In particular \(\int|D|^4\ll N^{2-\epsilon}\) would suffice at \(p=4\).

[P] For this very \(M\), a lower bound excludes every such global error-norm estimate. Partial summation of the PNT gives \(\sum_{n\le x}\Lambda(n)^2\sim x\log x\) and hence
\[
 \|S\|_2^2\sim \tfrac12 N\log N,\qquad
 \|M\|_2^2\le {N\over2}\sum_{q\le H}{\mu^2(q)\over\varphi(q)}
              ={N\over2}(\log H+O(1)).
\]
The first constant is \(\int_0^\infty e^{-2t}dt\); the second uses the full-line integral of \(|z|^{-2}\) as an upper bound on each arc. For the divisor sum write \(\mu^2(n)/\varphi(n)=(h*(1/n))(n)\) where \(h\) is multiplicative with \(h(p)=-h(p^2)=1/[p(p-1)]\), higher prime powers zero. Then \(\sum h=1\) and \(\sum |h(n)|\log(2n)<\infty\) by the Euler product. Convolution with the harmonic sum proves the stated estimate. Since \(\log H=\tfrac12\log N+O(1)\), the reverse triangle inequality gives
\[
 \|D\|_r\ge\|D\|_2\ge
 (1/\sqrt2-1/2-o(1))\sqrt{N\log N}\qquad(2\le r\le\infty).
                                                               \tag{6}
\]
In particular \(\int|D|^4\gg N^2\log^2 N\). The same reverse triangle bound holds for \(G\). This obstruction uses the genuine primes and the actual model. It leaves open improvements between the existing fourth-moment upper exponent \(5/2\) and the lower exponent 2.

[P] On the H2 complement the **unsigned** fourth moment of the prime sum itself has the same power floor. On \(A_y\) the H2 arc model has squared norm at most \((N/2)(\log H+O(1))\) with \(H\ll N^{1/16}\). Its error has squared norm \(\ll N T_y H^2\epsilon^2\ll N^{3/8}\log^2 N\) by the H2 uniform error and arc measure. Thus \(\int_{\mathbb T\setminus A_y}|S|^2\ge(15/32-o(1))N\log N\); Cauchy–Schwarz gives \(\int_{\mathbb T\setminus A_y}|S|^4\gg N^2\log^2 N\). For H1 the two major arcs have energy \(O(N)\) from their width and \(\|S\|_\infty\ll N\). [H1/H2 arc parameters and error](../../proof/strong_goldbach_research.md)

[P] More explicitly, Gallagher's inequality on a half-width \(\delta\) bounds the local energy of \(S^2\) by a constant times
\[
 \delta^2\int_{\mathbb R}\left|\sum_{x<n\le x+1/(2\delta)}
      e(an/q)e^{-n/N}\sum_{j+k=n}\Lambda(j)\Lambda(k)\right|^2 dx.
\]
On a single model arc one also has to subtract the terms from \(2SM-M^2\) to apply this to the squared error field \(D^2\). Using the pointwise linear approximation and the linear mean square on \(D\) gives precisely \(\int |D|^4\le \|D\|_\infty^2\|D\|_2^2\ll N^{5/2}\log^3 N\). Montgomery–Vaughan type spacing estimates improve the linear prime polynomial in (2), where its frequencies are \(\log n\). On the circle the frequencies of \(S^2\) are the integers \(j+k\), and all pairs with the same sum have already combined in its Fourier coefficient. Applying separation there requires a bound on the combined coefficients. No intermediate fourth-moment improvement for the genuine \(D\) follows from the inputs used here.

[U] Quantitatively, if \(B=\mathbb T\setminus A_y\) and \(b(Y,N)\) is an upper bound for the right side of (5) including its constant, a sufficient residual estimate is \(\Re\int_B S_{<Y}^2 e(-N\alpha)d\alpha\ge -N/3+b(Y,N)\). This allows cancellation among low zeros, pole and residue terms at the specified target. Equation (6) rules out reaching that conclusion by a global sub-square-root norm for the companion error.

[Q] Wave 2 supplies the beta exterior estimate, the local zero count and the abstract moment bounds. [Wave 2 §§1, 2, 4](B010_B011_ASTRA_ZEROPAIR_MOMENTS.md)

[P] A numerical check of (1) used \(N=128\), two ordinates \(14.134725,21.022040\) and three test ordinates \(17.3,20.7,25\). Direct log-gamma summation gave \(0.00454592553625+0.150235524533i\). Independent quadrature after \(y=\log(x/(1-x))\) differed by \(7.92\times10^{-15}\) in binary64. This checks the normalization on finite inputs. [Scratch script](/tmp/astra_w3_b011/check.py)

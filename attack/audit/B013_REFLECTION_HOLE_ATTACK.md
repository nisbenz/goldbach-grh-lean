# B-013 · Fourier reflection holes and the sign of the primitive energy

[I] Research audit, 27 November 2026. Tags apply to the entire following paragraph, display, table or code block. [Q] denotes a direct quotation, [P] a paraphrase of a cited repository source, [I] a derivation or a computation in this audit, and [U] an unproved input or unverified conclusion. All logarithms are natural. The transforms below use counting measure.

[I] **Verdict.** For every even \(M\ge4\), a reflection hole of size \(M/2-1\) exists with all nonzero Fourier coefficients bounded by \(\sqrt{1+(M/2)\log M}\). On units, both largest-conductor constructions work, including at \(p=3\). Their odd primitive energy exceeds their even primitive energy by exactly \(\varphi(N)^2\). Genuine prime weights violate the models' exact lower-conductor uniformity, but that distinction alone permits a reflection hole. Section 4 identifies the signed inequality that would force a prime pair and a cheaper sufficient test with a provable range limitation.

[P] The recorded finite Lean witness is the no-pair theorem for a specific subset of 15 residues modulo 32. The repository assigns this result the identifier GB-B013-PART. [Lean source](../lean/Goldbach/Reflection.lean) · [Claims map](../map/claims.json)

[U] B-013 remains open under the repository's strict-checker rule. The all-moduli inequalities below are paper derivations. The new finite Lean result in §5 has a local elaboration and dependency report only. Binary Goldbach, including a deduction under ERH, remains open.

## 1. Random additive hole

[I] Write \(e_M(u)=\exp(-2\pi i u/M)\), \(F(r)=\sum_{x\in D}e_M(rx)\), and \(C(t)=\sum_x1_D(x)1_D(t-x)\). Delete \(0,M/2\) and choose one of \(x,-x\) independently for each \(1\le x<M/2\). There are \(b=(M-2)/2\) coins. Every outcome has \(d=|D|=b\) and \(C(0)=0\). For \(r\ne0\), summing the omitted fixed-point phases gives
\[
 F(r)=\mu_r+iS_r,\qquad \mu_r=-\tfrac12(1+(-1)^r),\quad
 S_r=\sum_{x=1}^b\epsilon_x\sin(2\pi rx/M)
\]
with independent fair signs (their global sign convention is immaterial). Thus the real part is deterministic and \(|\mu_r|\le1\).

[I] At \(r=M/2\) the sine sum vanishes. At every other nonzero frequency its variance parameter is exactly \(V=\sum_{x=1}^b\sin^2(2\pi rx/M)=M/4\). Indeed the full ring sum is \(M/2\) by \(2r\ne0\) and the double-angle formula. The two fixed terms are zero and each remaining orbit contributes twice. Each summand has interval length \(2|\sin(2\pi rx/M)|\). Two-sided Hoeffding gives \(\Pr(|S_r|\ge t)\le2\exp(-t^2/(2V))=2\exp(-2t^2/M)\).

[I] Of the \(M-1\) nonzero frequencies, one is deterministic and the other \(M-2\) form conjugate pairs. The union bound is \((M-2)e^{-2t^2/M}\). Taking \(t=\sqrt{(M/2)\log M}\) makes the failure probability at most \((M-2)/M<1\), which proves the bound in the verdict. This is an existence statement. A version with success probability at least \(1-\delta\) follows by taking \(t=\sqrt{(M/2)\log((M-2)/\delta)}\), for \(0<\delta<1\). Both estimates imply the scale quoted in the source. [Original bound, §4](../../proof/strong_goldbach_research.md#4-attack-3--dispersion-zero-statistics-and-transference)

[I] Orthogonality gives \(\sum_r F(r)^2=M C(0)\) by expanding ordered pairs. Therefore \(\sum_{r\ne0}F(r)^2=-d^2\), with ordinary complex squares. Summing squared moduli would instead count the autocorrelation. For arbitrary complex \(f\) the algebraic identity persists, but its right-hand side need not be real or negative. For real nonnegative nonempty weights the right-hand side is strictly negative.

[I] Python 3.14.10, independent standard-library PRNG per modulus, seed \(13027+M\), one draw with no selection of a best trial. The last row reads the existing Lean set directly. “Exact sum” evaluates the nontrivial orthogonality kernel, \(M-1\) when \(x+y=0\) and \(-1\) otherwise, for each ordered pair. The last column independently evaluates the complex DFT in double precision and reports \(|\sum_{r\ne0}F(r)^2+d^2|\). The ratios use \(\sqrt{M\log M}\).

| Set or modulus | Size | C(0) | Peak | Peak / scale | Exact sum | DFT residual |
|---|---:|---:|---:|---:|---:|---:|
| 32 | 15 | 0 | 5.356151 | 0.508604 | -225 | 5.23e-14 |
| 64 | 31 | 0 | 8.334784 | 0.510877 | -961 | 3.29e-13 |
| 128 | 63 | 0 | 13.470042 | 0.540508 | -3969 | 9.39e-13 |
| 256 | 127 | 0 | 20.046373 | 0.532057 | -16129 | 4.22e-12 |
| 512 | 255 | 0 | 28.755775 | 0.508811 | -65025 | 1.69e-11 |
| 1024 | 511 | 0 | 59.268455 | 0.703495 | -261121 | 6.52e-11 |
| 4096 | 2047 | 0 | 100.592757 | 0.544984 | -4190209 | 1.02e-09 |
| Lean hole32 | 15 | 0 | 5.648543 | 0.536369 | -225 | 5.74e-14 |

## 2. The largest-conductor construction

[Q] “The top primitive family supplies precisely \(-\varphi(N)\) after normalization.” Here “top” refers to conductor \(N\) for powers of two and conductor \(p^2\) for \(N=2p^2\). [Persistent push, §5](../../proof/strong_goldbach_persistent_push.md#5-combining-detectors-on-sparse-conductors)

[I] Put \(G=U_N\), \(g=|G|\), \(R x=-x\), and let \(K\) be the kernel of the quotient map specified below. For the additive transform extend both \(f\) and \(1_G\) by zero off the units. On units, centering means subtracting one.

**[I] Powers of two.** For \(N=2^k,\ k\ge3\), use reduction to \(U_{N/2}\). Translation \(T x=x+N/2\) interchanges the two lifts of a unit and commutes with \(R\). A coincidence \(Tx=Rx\) would give \(2x\equiv N/2\pmod N\), impossible modulo 4 for odd \(x\). The free four-point blocks number \(g/4\). Choose \(\{x,RTx\}\) or \(\{Rx,Tx\}\) with equal probability, independently by block. Give the chosen sites weight 2. Each two-element fiber has mass 2 and each reflected pair has product zero. All proper conductors divide \(N/2\).

**[I] Twice an odd prime square.** Reduction identifies \(G\) with \(U_{p^2}\), since each residue modulo \(p^2\) has one odd lift modulo \(2p^2\). Reduce further to \(U_p\). The fibers \(F_a,F_{-a}\) are distinct and have size \(p\). For each of the \((p-1)/2\) pairs of fibers, delete one site and its negative, pair up the other \(p-1\) sites in the first fiber, and for each pair \(x,y\) select \(\{x,-y\}\) or \(\{y,-x\}\). Give each selected site weight \(w=2p/(p-1)\le3\). There are \(b=(p-1)^2/4\) independent blocks. Each fiber contains \((p-1)/2\) selected sites of total mass \(p\). Each reflected product is zero, including at both omitted sites. The only possible conductors are \(1,p,p^2\), since the factor at 2 is trivial. Thus the top characters modulo \(N\) are induced from primitive characters modulo \(p^2\). Calling them primitive *modulo* \(2p^2\) would give an empty family.

[I] At \(p=3\), the fibers modulo 3 in \(U_{18}\) are \(\{1,7,13\}\) and \(\{17,11,5\}\). Omit 1 and 17. Either \(\{7,5\}\) or \(\{13,11\}\), with weight 3, works. A binary 0/2 choice with a perfectly balanced fiber would require selecting \(3/2\) sites. This explains both the omitted lifts and the weight adjustment.

[I] In both families the fiber mass equals its cardinality. Every pulled-back nonprincipal character therefore has exactly zero coefficient by orthogonality on the quotient. The principal coefficient is exactly \(g\). More generally, \(f-1_G\) annihilates every function constant on the fibers, including additive characters that factor through the corresponding ring quotient (modulo \(N/2\) or \(2p\), respectively).

**[I] Simultaneous concentration.** For any unit-modulus phase \(z(x)\), let \(S=\sum_{x\in G}(f(x)-1)z(x)\). If a four-point block puts weight \(w\) on one of two complementary pairs, its centered random contribution is a fair sign times \((w/2)(z_1+z_2-z_3-z_4)\). Its magnitude is at most \(L=2w\). For \(N=2^k\), \(b=g/4,L=4\), and the mean vanishes. For \(N=2p^2\), \(L=4p/(p-1)\). There are exactly \(p-1\) omitted sites and \((p-1)^2\) other sites. At the former the mean of \(f-1\) is \(-1\), at the latter it is \(1/(p-1)\). Its \(\ell^1\) mass is \(D=2(p-1)\), so \(|\mathbb ES|\le D\); take \(D=0\) for powers of two. Treating the omitted sites as mean zero would lose this deterministic term.

[I] Each real or imaginary fluctuation is a sum of \(b\) independent centered variables with ranges of length at most \(2L\). If the complex modulus is at least \(t\), some component has magnitude at least \(t/\sqrt2\). The resulting tail is \(4e^{-t^2/(4bL^2)}\). Over \(H=N+g\) phases (all additive and multiplicative characters), the probability of any fluctuation of size at least \(2L\sqrt{b\log(8H)}\) is at most \(1/2\). The simultaneous bound is thus \(D+2L\sqrt{b\log(8H)}=O(\sqrt{N\log N})\) with absolute constants, since \(L\le6\), \(b\le N\), \(H\le2N\) and \(D\le\sqrt{2N}\). The argument permits a fixed deterministic choice of omitted sites and pairings.

**[I] Exact energy split.** Use \(\widehat f(\chi)=\sum_{x\in G} f(x)\overline{\chi(x)}\). Orthogonality gives \(g\sum_x f(x)f(-x)=\sum_\chi\chi(-1)|\widehat f(\chi)|^2\) for real \(f\). Write \(E,O\) for the sums of squared moduli over even and odd top characters respectively. The hole, lower-character vanishing and principal mass imply \(E-O=-g^2\). By Parseval, \(E+O=g\sum_x f(x)^2-g^2=(w-1)g^2\), since \(f\) takes values 0 and \(w\) and sums to \(g\). Hence

| Family | \(E/g^2\) | \(O/g^2\) | \((E-O)/g\) |
|---|---:|---:|---:|
| \(2^k\) | 0 | 1 | \(-g\) |
| \(2p^2\) | \(1/(p-1)\) | \(p/(p-1)\) | \(-g\) |

[I] For the finite checks below, the script verifies each fiber mass and reflected product using integer-scaled weights. It independently enumerates the full character table and computes its complex sums. In \(U_{2^k}=\langle-1\rangle\times\langle5\rangle\), the exponent on \(-1\) determines parity and an odd Fourier index on \(\langle5\rangle\) gives top conductor (its order-two element generates \(K\)). In cyclic \(U_{p^2}\), index parity determines parity and \(p\nmid j\) gives top conductor (the kernel of size \(p\) is generated by the generator to the \(p-1\) power). The script also computes \(E,O\) exactly as \((g/4)\sum_x(f(x)+f(-x)-2)^2\) and \((g/4)\sum_x(f(x)-f(-x))^2\) because the top projection of \(f\) is \(f-1\). Every row passed. The two peak columns are the maxima over **all** centered additive and multiplicative frequencies, in units of \(\sqrt{N\log N}\).

| N | g | Additive peak / scale | Multiplicative peak / scale | Exact signed top / g |
|---:|---:|---:|---:|---:|
| 8 | 4 | 0.69347 | 0.98071 | -4 |
| 16 | 8 | 0.78467 | 0.84932 | -8 |
| 32 | 16 | 0.82527 | 0.99254 | -16 |
| 64 | 32 | 1.06028 | 0.89166 | -32 |
| 128 | 64 | 1.01079 | 0.98376 | -64 |
| 256 | 128 | 1.03259 | 1.12458 | -128 |
| 512 | 256 | 0.88613 | 1.34879 | -256 |
| 1024 | 512 | 1.00227 | 0.94286 | -512 |
| 2048 | 1024 | 1.12282 | 1.05632 | -1024 |
| 18 | 6 | 0.78167 | 0.72039 | -6 |
| 50 | 20 | 0.99366 | 0.56527 | -20 |
| 98 | 42 | 0.78327 | 0.76754 | -42 |
| 242 | 110 | 0.98872 | 0.80141 | -110 |
| 338 | 156 | 0.93991 | 0.72106 | -156 |
| 578 | 272 | 0.86823 | 0.66473 | -272 |
| 1058 | 506 | 0.80298 | 0.97223 | -506 |

## 3. Genuine prime weights

[I] Use representatives \(1\le x<N\) restricted to \(G\). Here \(v=\Lambda\) assigns \(\log q\) to every prime power \(q^a\); the prime-only weight \(v=\theta\) assigns \(\log q\) at primes and zero elsewhere. These choices use the actual finite target interval. Let \(m=\sum_x v(x)\), \(L_0=\sum_{\mathrm{lower}\ \chi}\chi(-1)|\widehat v(\chi)|^2\), **including the principal**, and \(R_0=g\sum_xv(x)v(N-x)\). With the same top energies as above,
\[
 R_0=L_0+E-O.
\]
Division by \(m^2\) makes the principal contribution one for both prime weights and for the synthetic examples. Positive \(R_0\) for \(\theta\) is a prime-pair witness. A positive Mangoldt correlation can include proper prime powers. For even \(N>4\), a prime pair containing a nonunit would require both primes equal to a common prime divisor of \(N\), hence \(N=2q\). In these tested families \(N\ne2q\) for prime \(q\).

[I] The four entries for each weight below are respectively \(E,O,L_0,R_0\), divided by \(m^2\). They come from the complete character table and direct evaluation of the correlation. The last column is the integer prime-count test in §4. The difference in primitive energies can have either sign for primes. At \(N=16\), even dominates for \(\Lambda\), and odd dominates after removing proper powers. Lower-conductor terms can also shift the baseline substantially, e.g. \(L_0/m^2=0.75241\) for \(\Lambda\) at \(N=256\).

| N | Λ even | Λ odd | Λ lower | Λ correlation | θ even | θ odd | θ lower | θ correlation | Max fiber surplus |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 8 | 0.02682 | 0.27866 | 0.90492 | 0.65308 | 0.02682 | 0.27866 | 0.90492 | 0.65308 | 1 |
| 16 | 0.16351 | 0.10106 | 1.16590 | 1.22835 | 0.08444 | 0.19183 | 1.26257 | 1.15518 | 2 |
| 32 | 0.00945 | 0.27157 | 1.00072 | 0.73860 | 0.02173 | 0.39749 | 0.93687 | 0.56112 | 2 |
| 64 | 0.18603 | 0.27704 | 0.98195 | 0.89094 | 0.35453 | 0.32841 | 0.97870 | 1.00481 | 1 |
| 128 | 0.19511 | 0.40035 | 0.87948 | 0.67424 | 0.26341 | 0.56625 | 0.78719 | 0.48435 | 1 |
| 256 | 0.36393 | 0.40928 | 0.75241 | 0.70706 | 0.43126 | 0.44649 | 0.73430 | 0.71907 | 1 |
| 512 | 0.39305 | 0.60148 | 0.92297 | 0.71453 | 0.40963 | 0.68359 | 0.88946 | 0.61550 | 1 |
| 1024 | 0.51588 | 0.63737 | 0.80968 | 0.68819 | 0.57689 | 0.66478 | 0.81775 | 0.72986 | 1 |
| 2048 | 0.56732 | 0.73046 | 0.76098 | 0.59784 | 0.58774 | 0.78410 | 0.74620 | 0.54983 | 1 |
| 18 | 0.03189 | 0.17078 | 0.95788 | 0.81899 | 0.03189 | 0.17078 | 0.95788 | 0.81899 | 2 |
| 50 | 0.11019 | 0.27588 | 1.00516 | 0.83948 | 0.20317 | 0.39000 | 1.01449 | 0.82766 | 3 |
| 98 | 0.23364 | 0.51058 | 0.97870 | 0.70176 | 0.24189 | 0.66946 | 0.96600 | 0.53844 | 1 |
| 242 | 0.37805 | 0.70564 | 0.99912 | 0.67153 | 0.43263 | 0.80940 | 0.99625 | 0.61948 | 1 |
| 338 | 0.49555 | 0.79315 | 0.99586 | 0.69826 | 0.57681 | 0.89241 | 0.99332 | 0.67772 | -1 |
| 578 | 0.59312 | 0.93210 | 0.98738 | 0.64839 | 0.66629 | 1.03057 | 0.98745 | 0.62317 | -2 |
| 1058 | 0.76981 | 1.06949 | 0.98973 | 0.69005 | 0.80883 | 1.16817 | 0.98696 | 0.62762 | -6 |

**[I] A qualitative separator valid throughout both families.** Bertrand's postulate gives a prime \(N/2<q<N\). It is a unit, and \(q^2>N\). In the sum of \(\Lambda\) over its quotient fiber, the coefficient of \(\log q\) is one; in any other fiber it is zero. The fibers have equal size and there are at least two. Unique factorization after exponentiating precludes equality of those sums. The same argument applies to \(\theta\). Fourier inversion on the quotient now implies a nonzero lower nonprincipal coefficient for either prime weight at every such \(N\). This uses no ERH.

[I] In fact both weights have strictly positive even top energy. If it vanished, the even part \((v(x)+v(-x))/2\) would be constant within every quotient fiber. Take the site \(q\) above and a different lift in its fiber. The negative of \(q\) belongs to the *opposite* fiber (both quotients have distinct reflected fibers). Only the first reflected pair contributes \(\log q\). Unique factorization again forbids equality. This already distinguishes the prime weights from the power-of-two model; the odd-prime-square model itself has positive even top energy.

[I] Neither qualitative distinction forces overlap: perturb the weight of one selected site of the synthetic hole by a small positive amount. Its reflected site still has weight zero, its fiber mass now differs from the others, and its symmetrization varies within that fiber (in the power-of-two case it was previously constant). Renormalization restores mean one. An arbitrarily small perturbation changes each centered spectrum by an arbitrarily small amount for fixed \(N\). The missing distinction must constrain the **size and sign** of the residual.

## 4. What can force the center

**[I] A signed estimate with an exact threshold.** For \(\theta\), a pair exists in the units precisely when \(O-E<L_0\). For \(\Lambda\), let \(B_N\) upper-bound the contribution to \(\sum_x\Lambda(x)\Lambda(N-x)\) on units from pairs with at least one proper prime power, counting each ordered pair once. Then \(O-E<L_0-gB_N\) suffices for a prime pair. Using a separately proved upper bound makes this a sufficient inequality. With the exact nuisance mass this criterion is equivalent to the desired positivity. A uniform lower bound \((L_0+E-O)/m^2\ge\delta>0\), together with \(gB_N/m^2<\delta\), gives a margin. The synthetic hole attains equality at zero. A lower bound on each energy separately, or a positive principal term alone, cannot enforce the strict inequality.

**[I] A fiber pigeonhole test with a limitation.** For a quotient fiber \(F_a\) of size \(h\), let \(P_a\) count its primes. At least \(P_a+P_{-a}-h\) points of \(F_a\) belong to both the prime support and its reflection. Hence a positive maximum surplus forces a prime pair using individual counts. The synthetic support has nonpositive surplus in every fiber. Thirteen of the sixteen tested targets have positive surplus. The prime-only correlations at 338, 578 and 1058 are positive even though the surplus test misses them.

[I] For \(N=2p^2\) the same test **must** miss every \(p>1190\). For \(p>7\) the \(p\) odd lifts in one fiber form a progression of step \(2p\), coprime to 105. In each complete set of 105 consecutive lifts only \(\varphi(105)=48\) are coprime to 105. A remainder contains at most 48 coprime sites, and only the three primes 3, 5, 7 can contribute at noncoprime sites. Hence \(P_a\le48p/105+51\), uniformly in \(a\). This gives \(P_a+P_{-a}\le96p/105+102<p\) when \(p>1190\). The obstruction here is to this particular sufficient criterion.

**[I] Simultaneous neighboring centers.** For the additive model of §1 and any \(t\ne0\), at most four \(x\)'s involve a deleted fixed site in \((x,t-x)\). Among the rest, at most two solve \(2x=t\) and contribute expectation \(1/2\). Every other pair uses independent coins, since \(t-x=-x\) would require \(t=0\). Consequently \(\mathbb E C(t)=M/4+O(1)\) uniformly (absolute error at most 1). Flipping one coin changes at most four summands in \(C(t)\). The bounded-differences inequality gives
\[
 \Pr(|C(t)-\mathbb EC(t)|\ge s)\le 2\exp[-2s^2/(16b)].
\]
Take \(s=4\sqrt{b\log M}\), sum over \(M-1\) centers and also apply §1 with \(t_{\rm Fourier}=\sqrt{M\log M}\). The combined failure probability is \(O(1/M)\). Thus there exist holes with *every other center*, including both neighbors at offsets 2, within \(O(\sqrt{M\log M})\) of \(M/4\), and with all the small Fourier coefficients. In particular averages over a growing short interval can look typical despite the missing center. This is a cyclic example; it tests inferences from nearby counts.

**[I] Smoothness that would suffice.** On a cyclic group let \(K\) be nonnegative with mass one, set \(C=v*v\), and average \(A=\sum_t K(t) C(t)\). Fourier inversion at zero and at the shifted centers gives
\[
 |C(0)-A|\le M^{-1}\sum_r |\widehat v(r)|^2 |1-\widehat K(-r)|.
\]
A lower bound for \(A\) strictly exceeding this variation bound forces \(C(0)>0\). This requires control of the shift-sensitive spectral mass on the same scale as the averaged signal. For the holes with typical neighbors, averaging just those neighbors produces a variation of order \(M\). For the unit examples all tests constant on quotient fibers agree exactly with the mean, yet the lift-dependent terms erase the center. More localized major-arc phase information could be sufficient if its positive signed contribution exceeds the worst remaining negative contribution after prime-power subtraction. The examples test fiber-constant phases and individual coefficient bounds; no conclusion about arbitrary continuous major arcs is required.

**[I] Higher energies and ternary positivity.** The additive fourth moment is a sum of nonnegative terms for every hole. More quantitatively, if \(B=\max_{r\ne0}|F(r)|\), Parseval gives
\[
 \sum_t |C(t)-d^2/M|^2
 =M^{-1}\sum_{r\ne0}|F(r)|^4\le B^2(d-d^2/M).
\]
An upper bound strictly below \((d^2/M)^2\) would exclude even one zero. Mere nonnegativity supplies no such bound. In the ternary case the same hole satisfies \(|1_D^{*3}(t)-d^3/M|\le B(d-d^2/M)\) uniformly, since \(\sum_{r\ne0}|F(r)|^3\le B\sum_{r\ne0}|F(r)|^2\). For large \(M\), the ternary main term is of order \(M^2\), and its error is \(O(M^{3/2}\sqrt{\log M})\). Thus even positivity at *every ternary center* coexists with the missing binary center.

[P] The target-centered expansion in the repository gives a related sufficient signed inequality, H3, after bounding one-point terms and the proper-prime-power contribution. It identifies the even-minus-odd energy as the unestimated term. [Pointwise analysis, §5](../../proof/strong_goldbach_research.md#5-attack-4--centering-on-the-targets-reduced-residues)

[U] No estimate in the audited material proves the required pointwise signed margin for primes, with or without Dirichlet ERH. ERH specifies zero locations for genuine Dirichlet functions. The holes have no asserted Euler products or zeros. They disprove the inference from individual coefficient bounds, lower-conductor uniformity and principal mass; whether ERH implies a stronger joint estimate remains open.

## 5. Proposed finite Lean micro-lemma

[I] Use the eight canonical representatives for \(U_{16}\). On this domain \(16-x\) is the representative of \(-x\). Select 1, 3, 5 and 7 with weight 2. Every unit fiber modulo 8 has one selected and one unselected lift. The third conjunct below tests *every* complex function on the reduced representatives. Taking \(h\) to be the conjugate of a character of \(U_8\), extended arbitrarily to the other naturals, gives exact centered vanishing. For a nonprincipal character, orthogonality gives zero uncentered coefficient as well. The first two conjuncts check reflection and mean one. The proof uses finite evaluation for those two conjuncts and expands the last sum so that identical values of \(h\) cancel.

```lean
import Mathlib

namespace ReflectionAudit

private def units16 : Finset ℕ := {1, 3, 5, 7, 9, 11, 13, 15}
private def weight16 (x : ℕ) : ℕ := if x ∈ ({1, 3, 5, 7} : Finset ℕ) then 2 else 0

theorem reflection16_lower_tests :
    (∀ x ∈ units16, weight16 x * weight16 (16 - x) = 0) ∧
    (∑ x ∈ units16, weight16 x) = units16.card ∧
    (∀ h : ℕ → ℂ, (∑ x ∈ units16, ((weight16 x : ℂ) - 1) * h (x % 8)) = 0) := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  norm_num [units16, weight16, Finset.sum_insert]
  ring

end ReflectionAudit
```

[I] The declaration above elaborated and compiled in scratch space with the local v4.16.0 mathlib installation. Loading its compiled module and asking Lean for the theorem dependencies returned the following output (exit 0).

```text
'ReflectionAudit.reflection16_lower_tests' depends on axioms: [propext, Classical.choice, Quot.sound]
```

[U] The proposed statement concerns one deterministic modulus. A repository strict-checker verdict for the general B-013 statement remains outstanding. The dependency printout concerns only the named local micro-lemma.

## Reproducing the computations

[I] From the repository root run `python3 /tmp/astra_b013/verify.py`. The command emits all the data in §§1–3 and raises an assertion on a failed identity or bound. The additive tests use direct DFTs. The exact checks use integers and rational arithmetic; estimates involving complex exponentials or logarithms use double precision. The Python source is included here so that the computation is recoverable after scratch cleanup. To recreate the script from this Markdown, copy the Python block below. SHA-256 of the script including its final newline is `eb98cde5a079ae241c79317185ca11d40cd20fb77af0c19cc0586cdec6e6f13f`.

<details>
<summary>Python verifier</summary>

```python
"""Run with Python 3.10+ from the repository root. No third-party packages."""
import cmath
import math
import random
import re
from fractions import Fraction
from pathlib import Path

SEED = 13027


def roots(n):
    return [cmath.exp(-2j * math.pi * j / n) for j in range(n)]


def dft(values):
    n = len(values)
    table = roots(n)
    support = [(j, x) for j, x in enumerate(values) if x]
    return [sum(x * table[(j * r) % n] for j, x in support) for r in range(n)]


def additive_case(m, points):
    a = [int(j in points) for j in range(m)]
    d = len(points)
    assert d == m // 2 - 1
    pair0 = sum(a[j] * a[-j] for j in range(m))
    assert pair0 == 0
    # Exact evaluation via the nontrivial-character orthogonality kernel.
    exact = sum(m - 1 if (x + y) % m == 0 else -1 for x in points for y in points)
    assert exact == -(d * d)
    F = dft(a)
    peak = max(abs(z) for z in F[1:])
    residual = abs(sum(z*z for z in F[1:]) + d*d)
    assert residual < 1e-8 * max(1, d*d)
    assert peak <= math.sqrt(1 + m*math.log(m)/2)
    print(f'{m:4} {d:4} {pair0} {peak:10.6f} {peak/math.sqrt(m*math.log(m)):.6f}'
          f' {exact:10} {residual:.3g}')


def units_hole(n, p):
    rng = random.Random(SEED + n)
    U = [x for x in range(n) if math.gcd(x, n) == 1]
    Uset = set(U)
    den = (p-1) if p else 1
    W = dict.fromkeys(U, 0)  # weight times den
    if p is None:
        half = n // 2
        seen = set()
        for x in U:
            if x in seen:
                continue
            y, v, z = (-x) % n, (x+half) % n, (half-x) % n
            block = {x, y, v, z}
            assert len(block) == 4 and seen.isdisjoint(block)
            seen.update(block)
            i, j = rng.choice([(x, z), (y, v)])
            W[i] = W[j] = 2
        assert seen == Uset
        quotient = half
    else:
        quotient = p
        for a in range(1, (p+1)//2):
            fiber = [x for x in U if x % p == a]
            assert len(fiber) == p
            for x, y in zip(fiber[1::2], fiber[2::2]):
                i, j = rng.choice([(x, (-y) % n), (y, (-x) % n)])
                W[i] = W[j] = 2*p
    assert all(W[x]*W[n-x] == 0 for x in U)
    for a in {x % quotient for x in U}:
        fiber = [x for x in U if x % quotient == a]
        assert sum(W[x] for x in fiber) == len(fiber)*den
    return U, W, den


def char_energies(n, p, U, values):
    """Full character table via cyclic coordinates; output raw unnormalised energies."""
    g = len(U)
    if p:
        # Choose the least generator in U_n, isomorphic to U_(p^2).
        b = next(b for b in U if len({pow(b, j, n) for j in range(g)}) == g)
        vec = [values[pow(b, j, n)] for j in range(g)]
        specs = [(j % p != 0, j % 2, c) for j, c in enumerate(dft(vec))]
    else:
        h = g//2
        pos = [pow(5, j, n) for j in range(h)]
        assert len(set(pos + [n-x for x in pos])) == g
        specs = [(bool(j % 2), s, c) for s in range(2)
                 for j, c in enumerate(dft([values[x] + (-1)**s * values[n-x]
                                              for x in pos]))]
    even = sum(abs(z)**2 for top, odd, z in specs if top and not odd)
    odd = sum(abs(z)**2 for top, odd, z in specs if top and odd)
    lower = sum((-1)**odd * abs(z)**2 for top, odd, z in specs if not top)
    direct = sum(values[x]*values[n-x] for x in U)
    assert math.isclose(lower + even - odd, g*direct,
                        abs_tol=1e-8*max(1, sum(values.values())**2))
    return even, odd, lower, specs


def prime_weights(n):
    theta = dict.fromkeys(range(n), 0.0)
    mangoldt = theta.copy()
    for q in range(2, n):
        if any(q % d == 0 for d in range(2, math.isqrt(q)+1)):
            continue
        theta[q] = math.log(q)
        a = q
        while a < n:
            mangoldt[a] = theta[q]
            a *= q
    return theta, mangoldt


def conductor_case(n, p):
    U, W, den = units_hole(n, p)
    g = len(U)
    scale = math.sqrt(n*math.log(n))
    f = {x: W[x]/den for x in U}
    bal = [0.0]*n
    for x in U:
        bal[x] = f[x]-1
    A = max(abs(z) for z in dft(bal))
    even, odd, _, specs = char_energies(n, p, U, f)
    # Dropping the principal removes the constant on U in the multiplicative transform.
    topmax = max(abs(z) for top, _, z in specs if top)
    assert abs(specs[0][2] - g) < 1e-7  # trivial character comes first
    assert all(abs(z) < 1e-7 for top, _, z in specs[1:] if not top)
    # Exact Parseval for the top projection, in integer arithmetic before division.
    e = Fraction(g*sum((W[x]+W[n-x]-2*den)**2 for x in U), 4*den**2)
    o = Fraction(g*sum((W[x]-W[n-x])**2 for x in U), 4*den**2)
    assert e == (Fraction(g*g, p-1) if p else 0) and o-e == g*g
    assert math.isclose(e, even, abs_tol=1e-6)
    assert math.isclose(o, odd, abs_tol=1e-6)
    blocks = ((p-1)**2//4 if p else g//4)
    c = (4*p/(p-1) if p else 4)
    bias = 2*(p-1) if p else 0
    threshold = bias + 2*c*math.sqrt(blocks*math.log(8*(n+g)))
    assert max(A, topmax) <= threshold
    row = []
    for v in reversed(prime_weights(n)):  # Lambda, then prime-only theta
        v = {x:v[x] for x in U}
        E, O, L, _ = char_energies(n, p, U, v)
        m2 = sum(v.values())**2
        row.extend([E/m2, O/m2, L/m2, g*sum(v[x]*v[n-x] for x in U)/m2])
    qmod = p if p else n//2
    fiber_size = p if p else 2
    primes, _ = prime_weights(n)
    counts = {a: sum(primes[x] > 0 for x in U if x % qmod == a)
              for a in {x % qmod for x in U}}
    surplus = max(cnt + counts[(-a) % qmod] - fiber_size for a, cnt in counts.items())
    return (f'{n:4} {g:4} {A/scale:.5f} {topmax/scale:.5f} {-g:5}',
            f'{n:4} ' + ' '.join(f'{y:.5f}' for y in row) + f' {surplus:3}')


if __name__ == '__main__':
    print('M d C(0) peak peak/scale exact_sum DFT_residual')
    for m in (32,64,128,256,512,1024,4096):
        rng = random.Random(SEED+m)
        additive_case(m, {rng.choice((x,m-x)) for x in range(1, m//2)})
    src = Path('attack/lean/Goldbach/Reflection.lean').read_text()
    data = re.search(r'def hole32 : Finset ℕ := \{([^}]+)\}', src)[1]
    print('hole32')
    additive_case(32, set(map(int, data.split(','))))
    rows = [conductor_case(2**k,None) for k in range(3,12)]
    rows += [conductor_case(2*p*p,p) for p in (3,5,7,11,13,17,23)]
    print('N phi peakAdd/scale peakMult/scale exact_signed_top/phi')
    print('\n'.join(row[0] for row in rows))
    print('N Lambda(E O L R)/mass^2 theta(E O L R)/mass^2; R includes phi; max fiber surplus')
    print('\n'.join(row[1] for row in rows))
```

</details>

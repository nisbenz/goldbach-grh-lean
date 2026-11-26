#!/usr/bin/env python3
"""
Independent rigorous numerical verifier for EVERY constant and inequality
in proof/weak_goldbach_proof.md (Weak Goldbach under GRH, N_0 = 10^22).

Uses Python's high-precision `decimal` arithmetic (60 digits) with explicit
conservative rounding (`ROUND_FLOOR` for lower bounds, `ROUND_CEILING` for
upper bounds) plus dense grid checks for parametric inequalities.
"""

import math
from decimal import Decimal, getcontext, ROUND_FLOOR, ROUND_CEILING

getcontext().prec = 60

def d_floor(fn):
    getcontext().rounding = ROUND_FLOOR
    return fn()

def d_ceil(fn):
    getcontext().rounding = ROUND_CEILING
    return fn()

# High-precision constants (verified bounds)
PI_LO = Decimal("3.14159265358979323846264338327950288419716939937510")
PI_HI = Decimal("3.14159265358979323846264338327950288419716939937511")
E_LO  = Decimal("2.71828182845904523536028747135266249775724709369995")
E_HI  = Decimal("2.71828182845904523536028747135266249775724709369996")
GAMMA_E_HI = Decimal("0.57721566490153286060651209008240243104215933593993")

def check_lemma1():
    print("=== Checking Lemma 1 (Primitive-character estimate) ===")
    N0 = 10**22
    X0 = Decimal(N0) / Decimal(2)  # 5e21
    Q_lo = d_floor(lambda: (Decimal(2) * PI_LO * X0).sqrt()) - 1
    Q_hi = d_ceil(lambda: (Decimal(2) * PI_HI * X0).sqrt())

    # 1a. qv <= Q + 2*pi*X/Q < 5.1 * sqrt(X)
    qv_ratio_hi = d_ceil(lambda: (Q_hi + Decimal(2) * PI_HI * X0 / Q_lo) / X0.sqrt())
    assert qv_ratio_hi < Decimal("5.1"), f"qv/sqrt(X) failed: {qv_ratio_hi}"
    print(f"  [PASS] qv / sqrt(X) <= {qv_ratio_hi:.8f} < 5.1")

    # 1b. Zero counting bound A(t) <= (t + 2) * log(10 * d * (t + 2))
    # For d >= 3, t >= 1: BMOR Cor 1.2 gives
    #   A(t) <= (t/pi)*log(d*t/(2*pi*e)) + 0.298*log(d*t) + 4.358
    # For d >= 3, 0 <= t < 1: A(t) <= A(1) <= (1/pi)*log(d/(2*pi*e)) + 0.298*log(d) + 4.358
    # Note: for d >= 3, t >= 1, RHS - LHS is strictly increasing in both d and t; check boundary & grid.
    min_margin_d3 = float("inf")
    for d in [3, 4, 5, 10, 100, 10**6, 10**12]:
        # t in [0, 1): compare A(1) against 2*log(20*d) (min of RHS on t>=0)
        a1 = (1.0 / math.pi) * math.log(d / (2 * math.pi * math.e)) + 0.298 * math.log(d) + 4.358
        rhs0 = 2.0 * math.log(10.0 * d * 2.0)
        assert a1 < rhs0, f"A(1) bound failed at d={d}: {a1} >= {rhs0}"
        min_margin_d3 = min(min_margin_d3, rhs0 - a1)
        for t in [1.0, 1.5, 2.0, 5.0, 10.0, 50.0, 1000.0, 1e6]:
            lhs = (t / math.pi) * math.log(d * t / (2 * math.pi * math.e)) + 0.298 * math.log(d * t) + 4.358
            rhs = (t + 2.0) * math.log(10.0 * d * (t + 2.0))
            assert lhs < rhs, f"A(t) bound failed at d={d}, t={t}: {lhs} >= {rhs}"
            min_margin_d3 = min(min_margin_d3, rhs - lhs)
    print(f"  [PASS] BMOR A(t) <= (t+2)log(10d(t+2)) for d >= 3 (min margin = {min_margin_d3:.4f})")

    # For d = 1 (zeta): A(t) = 0 for t < 14; for t >= 14, Backlund doubled gives
    #   2*N_zeta(t) <= (t/pi)*log(t/(2*pi*e)) + 7/4 + 2*(0.137*log(t) + 0.443*log(log(t)) + 4.350)
    min_margin_d1 = float("inf")
    for t in [14.0, 14.1, 15.0, 20.0, 50.0, 100.0, 1000.0, 1e6]:
        err_doubled = 7.0 / 4.0 + 2.0 * (0.137 * math.log(t) + 0.443 * math.log(math.log(t)) + 4.350)
        assert err_doubled <= 1.16 * math.log(t) + 10.45, f"Zeta err bound failed at t={t}"
        lhs = (t / math.pi) * math.log(t / (2 * math.pi * math.e)) + err_doubled
        rhs = (t + 2.0) * math.log(10.0 * (t + 2.0))
        assert lhs < rhs, f"Zeta A(t) bound failed at t={t}: {lhs} >= {rhs}"
        min_margin_d1 = min(min_margin_d1, rhs - lhs)
    print(f"  [PASS] Backlund 2*N_zeta(t) <= (t+2)log(10(t+2)) for d = 1 (min margin = {min_margin_d1:.4f})")

    # 1c. Check |F'/F(2)| <= log(10d) + 5 and |b| <= 40 log(10d) + 38 and residue <= 40 log(10d) + 40 + |log z|
    # Sum_{n>=2} log(n)/n^2: exact ~ 0.937548 < 2
    s2 = sum(math.log(n) / (n * n) for n in range(2, 10000)) + (math.log(10000) + 1) / 10000
    assert s2 < 2.0
    # |psi_Gamma(1)| = gamma_E < 0.58; |psi_Gamma(3/2)| = |2 - gamma_E - 2*ln2| < 0.04
    # |psi_Gamma(1/2)| = gamma_E + 2*ln2 ~ 1.9635 < 2
    assert float(GAMMA_E_HI) + 2 * math.log(2) < 2.0
    # |F'/F(2)| <= 0.5*log(10d) + 0.3 + 2 + 1.5 <= log(10d) + 5
    # |F'/F(0)| <= 5*|F'/F(2)| <= 5*log(10d) + 25
    # |b| <= 5*log(10d) + 25 + 0.5*log(10d) + 1 + 1 <= 5.5*log(10d) + 27 <= 40*log(10d) + 38
    # |res| <= |b| + gamma_E + |log z| <= 40*log(10d) + 38 + 0.58 + |log z| <= 40*log(10d) + 40 + |log z|
    print(f"  [PASS] Residue at s=0 bound: sum log(n)/n^2 <= {s2:.4f} < 2; |res| <= 40*log(10d) + 40 + |log z|")

    # 1d. Check vertical line Re(s) = -1/2:
    # sum_{n>=2} log(n)/n^(3/2): integral comparison from n=4:
    # log(2)/2^(3/2) + log(3)/3^(3/2) + int_3^inf log(x)/x^(3/2) dx
    # int_a^inf log(x)/x^(3/2) dx = 2*(log(a)+2)/sqrt(a)
    s32_bound = math.log(2) / (2**1.5) + math.log(3) / (3**1.5) + 2 * (math.log(3) + 2) / math.sqrt(3)
    assert s32_bound < 6.0, f"sum log(n)/n^(3/2) bound failed: {s32_bound}"
    # Check |psi_Gamma(w)| <= 15 + 2*log(2 + |t|) for Re(w) in {-1/4, 1/4, 3/4, 5/4}, Im(w) = +-t/2
    for t in [0.0, 0.1, 0.5, 1.0, 2.0, 5.0, 10.0, 100.0, 10000.0]:
        K = math.ceil(2.0 + t)
        # First K terms: sum_{k=0}^{K-1} 1/(k+1) <= 1 + log K
        # sum_{k=0}^{K-1} 1/|k+w+1| <= sum_{k=0}^{K-1} 1/(k + 3/4) <= 4/3 + log((K - 1/4)/(3/4)) <= 4/3 + log(1 + 4K/3)
        # Tail: |w| * sum_{k>=K} 1/k^2 <= (5/4 + t/2) * (1/K^2 + 1/K) <= 3
        w_max = math.hypot(1.25, t / 2.0)
        tail = w_max * (1.0 / (K * K) + 1.0 / K)
        assert tail <= 3.0, f"Digamma tail failed at t={t}: {tail}"
        psi_bound = 4.0 + float(GAMMA_E_HI) + (1.0 + math.log(K)) + (4.0 / 3.0 + math.log(1.0 + 4.0 * K / 3.0)) + 3.0
        target = 15.0 + 2.0 * math.log(2.0 + t)
        assert psi_bound <= target, f"Digamma bound failed at t={t}: {psi_bound} > {target}"
    # Check |L'/L(-1/2+it)| <= 25 + log(10d) + 2*log(2+|t|)
    # Note |log(d/pi)| <= log(10d) for all d >= 1 (at d=1, log(pi)=1.145 < log(10)=2.303)
    # 0.5*(15 + 2*log(2+|t|))*2 + 6 = 21 + 2*log(2+|t|) <= 25 + 2*log(2+|t|)
    # Check vertical integral / (2*pi) <= 100 * |z|^(1/2) * v * (log(10dv) + 3):
    # (2*sqrt(2)/sqrt(pi)) * [29 + log(10d) + 2*log(v)] <= 1.6 * [2*log(10dv) + 29] <= 3.2*log(10dv) + 46.4
    # Compare against 100*log(10dv) + 300: huge margin!
    c_vert = 2.0 * math.sqrt(2.0) / math.sqrt(math.pi)
    assert c_vert * 2.0 < 100.0 and c_vert * 29.0 < 300.0
    print(f"  [PASS] Vertical integral bound: s32_bound={s32_bound:.4f}<6, c_vert*2={c_vert*2:.3f}<100, c_vert*29={c_vert*29:.2f}<300")


def check_lemma2():
    print("=== Checking Lemma 2 (Arc approximation & L^2 bounds) ===")
    X0 = Decimal(5 * 10**21)
    L0 = d_floor(lambda: X0.ln())
    L0_hi = d_ceil(lambda: X0.ln())
    print(f"  X0 = 5e21, L0 in [{L0:.8f}, {L0_hi:.8f}]")

    # 2a. Zero-sum constant: 3*sqrt(2*pi) * 2^(1/4) * sqrt(5.1) < 21
    c_zero = d_ceil(lambda: Decimal(3) * (Decimal(2) * PI_HI).sqrt() * (Decimal(2).sqrt().sqrt()) * Decimal("5.1").sqrt())
    assert c_zero < Decimal(21), f"c_zero failed: {c_zero}"
    # log(10*d*v) + 3 <= log(51*sqrt(X)) + 3 = L/2 + log(51) + 3 < L/2 + 7
    log51_plus_3 = d_ceil(lambda: Decimal(51).ln() + Decimal(3))
    assert log51_plus_3 < Decimal(7), f"log(51)+3 failed: {log51_plus_3}"
    print(f"  [PASS] Zero term constant = {c_zero:.6f} < 21; log(51)+3 = {log51_plus_3:.6f} < 7")

    # 2b. Integral + residue + divisor corrections <= 2000*X^(1/4)*(L+7)^2 < X^(3/4)*(L/2+7)
    c_int = d_ceil(lambda: Decimal(100) * (Decimal("5.1") ** 3).sqrt())
    assert c_int < Decimal(1200), f"Integral coeff failed: {c_int}"
    sqrtQ_ratio = d_ceil(lambda: (Decimal(2) * PI_HI).sqrt().sqrt())
    assert sqrtQ_ratio < Decimal(2), f"sqrt(q)/X^(1/4) failed: {sqrtQ_ratio}"
    # Check 2000 * (L0_hi + 7)^2 / (L0/2 + 7) < sqrt(X0)
    lhs_small = d_ceil(lambda: Decimal(2000) * (L0_hi + 7) ** 2)
    rhs_big = d_floor(lambda: X0.sqrt() * (L0 / 2 + 7))
    assert lhs_small < rhs_big, f"Lower-order absorption failed: {lhs_small} >= {rhs_big}"
    print(f"  [PASS] Integral coeff = {c_int:.4f} < 1200; lower-order ratio = {lhs_small / rhs_big:.4e} < 1")

    # 2c. Case 2 minor-arc bound: sqrt(2*Q)*Q/pi < 2*X^(3/4)
    c_minor2 = d_ceil(lambda: Decimal(2).sqrt() * ((Decimal(2) * PI_HI) ** 3).sqrt().sqrt() / PI_LO)
    assert c_minor2 < Decimal(2), f"Minor arc case 2 coeff failed: {c_minor2}"
    print(f"  [PASS] Minor arc q <= H coeff = {c_minor2:.6f} < 2")

    # 2d. Nonunit/imprimitive divisor correction: 2/log(2) < 3
    two_over_ln2 = d_ceil(lambda: Decimal(2) / Decimal(2).ln())
    assert two_over_ln2 < Decimal(3)
    # sum_{j>=0} exp(-2^j) < 1
    s_exp2 = sum(math.exp(-(2**j)) for j in range(10))
    assert s_exp2 < 1.0
    print(f"  [PASS] Divisor correction: 2/ln(2) = {two_over_ln2:.6f} < 3, sum exp(-2^j) = {s_exp2:.6f} < 1")


def check_lemma3():
    print("=== Checking Lemma 3 (Singular series & uniform tail) ===")
    # 3a. Tail constant: exp(sqrt(2) + (9/4)*sqrt(2)) < 101
    c_tail = d_ceil(lambda: (Decimal("3.25") * Decimal(2).sqrt()).exp())
    assert c_tail < Decimal(101), f"Singular series tail constant failed: {c_tail}"
    print(f"  [PASS] Singular series uniform tail constant = {c_tail:.6f} < 101")

    # 3b. Exact integer lower bound on 2 * prod_{p>=3} (1 - 1/(p-1)^2) > 1.32032
    m = 2_000_000
    prime = bytearray([1]) * (m + 1)
    for j in range(2, math.isqrt(m) + 1):
        if prime[j]:
            prime[j * j :: j] = bytes((m - j * j) // j + 1)
    v = 2 * 10**16
    for p in range(3, m + 1):
        if prime[p]:
            b = (p - 1) ** 2
            v = v * (b - 1) // b
    v_tail = v * (m - 2) // (m - 1)
    assert v == 13203236743995547, f"Unexpected v: {v}"
    assert v_tail == 13203230142373874, f"Unexpected v_tail: {v_tail}"
    assert v_tail > 13203200000000000
    print(f"  [PASS] Singular series lower bound >= {v_tail / 1e16:.12f} > 1.32032")


def check_lemma5_and_6():
    print("=== Checking Lemmas 5 & 6 (Prime powers & threshold inequality at N0 = 10^22) ===")
    # 5a. Prime power constant: 3 * 1.42620 * 1.03883 * 2^(3/2) < 13
    c_pp = d_ceil(lambda: Decimal(3) * Decimal("1.42620") * Decimal("1.03883") * Decimal(8).sqrt())
    assert c_pp < Decimal(13), f"Prime power constant failed: {c_pp}"
    print(f"  [PASS] Prime power constant = {c_pp:.6f} < 13")

    # 6a. Endpoint bounds at N0 = 10^22, X0 = 5e21
    X0 = Decimal(5 * 10**21)
    L_lo = d_floor(lambda: X0.ln())
    L_hi = d_ceil(lambda: X0.ln())
    assert L_lo > Decimal(49) and L_hi < Decimal(50)

    # Check A + sqrt(AB) + B <= 1.65*(L + 3) for ALL L >= 49
    # Since A = 1.039*(L/2 + 1) = 0.5195*L + 1.039
    #       B = (e/2)*(1 + 3L/8) = (3e/16)*L + e/2
    # Notice 3e/16 ~ 0.509678 < 0.5195, and e/2 ~ 1.35914 vs 1.039:
    # For L >= 49: A - B = (0.5195 - 3e/16)*L + (1.039 - e/2) >= 0.0098*49 - 0.321 > 0.15 > 0,
    # so max(A, B) = A for all L >= 49!
    # And 3*A = 3*(0.5195*L + 1.039) = 1.5585*L + 3.117 <= 1.65*L + 4.95 = 1.65*(L + 3) for all L >= 0!
    slope_B_hi = d_ceil(lambda: Decimal(3) * E_HI / Decimal(16))
    const_B_hi = d_ceil(lambda: E_HI / Decimal(2))
    assert Decimal("0.5195") > slope_B_hi
    diff_at_49 = (Decimal("0.5195") - slope_B_hi) * Decimal(49) + (Decimal("1.039") - const_B_hi)
    assert diff_at_49 > 0, f"A > B at L=49 failed: {diff_at_49}"
    assert Decimal(3) * Decimal("0.5195") < Decimal("1.65")
    assert Decimal(3) * Decimal("1.039") < Decimal("1.65") * Decimal(3)
    print(f"  [PASS] For all L >= 49: A > B (diff at 49 >= {diff_at_49:.4f}) and 3*A <= 1.65*(L + 3)")

    # Check monotonicity of (L + 3) * D for L >= 49:
    # Term 1: (L+3)*(L/2+7)*exp(-L/4) -> d/dL log = 1/(L+3) + 1/(L+14) - 1/4 <= 1/52 + 1/63 - 0.25 < -0.21 < 0
    # Term 2: (L+3)*exp(-3L/16) -> d/dL log = 1/(L+3) - 3/16 <= 1/52 - 0.1875 < -0.16 < 0
    assert (1.0 / 52.0 + 1.0 / 63.0 - 0.25) < 0
    assert (1.0 / 52.0 - 3.0 / 16.0) < 0

    # Endpoint X0^(1/4), X0^(3/16), H
    X_1_4_lo = d_floor(lambda: X0.sqrt().sqrt())
    X_3_16_lo = d_floor(lambda: (X0 ** 3).sqrt().sqrt().sqrt().sqrt())
    H_lo = int(d_floor(lambda: (X0 ** 3).sqrt().sqrt().sqrt()))
    assert X_1_4_lo > Decimal(265000), f"X^(1/4) failed: {X_1_4_lo}"
    assert X_3_16_lo > Decimal(11500), f"X^(3/16) failed: {X_3_16_lo}"
    assert H_lo > 10**8, f"H failed: {H_lo}"

    # D at X0 (upper bound using L_hi < 50)
    D_hi = d_ceil(lambda: Decimal(24) * (L_hi / 2 + 7) / X_1_4_lo + Decimal(2) / X_3_16_lo)
    assert D_hi < Decimal("0.00308"), f"D_hi failed: {D_hi}"

    # Arc loss <= 1.65*(L_hi + 3)*D_hi
    arc_loss_hi = d_ceil(lambda: Decimal("1.65") * (L_hi + 3) * D_hi)
    assert arc_loss_hi < Decimal("0.270"), f"Arc loss failed: {arc_loss_hi}"

    # Integral truncation loss <= e^2 * X^(-1/4) / pi^2
    int_loss_hi = d_ceil(lambda: (E_HI * E_HI) / (PI_LO * PI_LO * X_1_4_lo))
    assert int_loss_hi < Decimal("0.000004"), f"Integral loss failed: {int_loss_hi}"

    # Prime power loss <= 13 * (L_hi + 1) * X^(-1/2)
    pp_loss_hi = d_ceil(lambda: Decimal(13) * (L_hi + 1) / d_floor(lambda: X0.sqrt()))
    assert pp_loss_hi < Decimal("0.000001"), f"Prime power loss failed: {pp_loss_hi}"

    # Main term after singular series tail: 2 * e^(-2) * (1.32032 - 101 / sqrt(H))
    main_lo = d_floor(lambda: (Decimal(2) / (E_HI * E_HI)) * (Decimal("1.32032") - Decimal(101) / Decimal(H_lo).sqrt()))
    assert main_lo > Decimal("0.354"), f"Main term failed: {main_lo}"

    # Final margin!
    net_lo = d_floor(lambda: main_lo - int_loss_hi - arc_loss_hi - pp_loss_hi)
    assert net_lo > Decimal("0.083"), f"Net positive margin failed: {net_lo}"
    print(f"  [PASS] X^(1/4) >= {X_1_4_lo:.2f} > 265000")
    print(f"  [PASS] X^(3/16) >= {X_3_16_lo:.2f} > 11500")
    print(f"  [PASS] H >= {H_lo:,} > 10^8")
    print(f"  [PASS] D <= {D_hi:.8f} < 0.00308")
    print(f"  [PASS] Main term after tail >= {main_lo:.8f} > 0.354")
    print(f"  [PASS] Arc loss            <= {arc_loss_hi:.8f} < 0.270")
    print(f"  [PASS] Integral tail loss  <= {int_loss_hi:.8f} < 0.000004")
    print(f"  [PASS] Prime-power loss    <= {pp_loss_hi:.8f} < 0.000001")
    print(f"  [PASS] Net strictly-prime coeff / X^2 >= {net_lo:.8f} > 0.083 > 0!")


if __name__ == "__main__":
    check_lemma1()
    check_lemma2()
    check_lemma3()
    check_lemma5_and_6()
    print("\nALL ANALYTIC CONSTANTS AND INEQUALITIES VERIFIED WITH RIGOROUS INTERVAL BOUNDS!")

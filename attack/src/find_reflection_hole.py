#!/usr/bin/env python3
"""Find an explicit reflection-hole set D in Z/MZ: (1_D*1_D)(0)=0 with small nonzero Fourier coefficients.

Construction from strong_goldbach_research.md §4: from each two-point orbit {x,-x} choose one
point; omit the fixed points (0 and M/2 for M even). Verify the convolution and Fourier bounds.

Usage: python3 src/find_reflection_hole.py --m 32 --seed 0
"""
import argparse, cmath, math, random

def search(M, seed, tries=20000, threshold_factor=6):
    fixed = {0, M // 2}
    orbits = []
    seen = set()
    for x in range(M):
        if x in fixed or x in seen: continue
        y = (-x) % M
        orbits.append((x, y)); seen.add(x); seen.add(y)
    rng = random.Random(seed)
    best = None
    for _ in range(tries):
        D = sorted(rng.choice(o) for o in orbits)
        # counting convolution at 0: #{a in D : -a in D} must be 0
        conv0 = sum(1 for a in D if (-a) % M in set(D))
        if conv0 != 0: continue
        # unnormalized Fourier coefficients
        coeffs = []
        for r in range(1, M):
            s = sum(cmath.exp(2j * math.pi * r * x / M) for x in D)
            coeffs.append(abs(s))
        mx = max(coeffs)
        thresh = threshold_factor * math.sqrt(M * math.log(M)) + 1
        if best is None or mx < best[0]: best = (mx, D, thresh, coeffs)
        if mx <= thresh: return D, mx, thresh, True
    return best[1], best[0], best[2], False

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--m", type=int, default=32)
    ap.add_argument("--seed", type=int, default=0)
    a = ap.parse_args()
    D, mx, thresh, ok = search(a.m, a.seed)
    print(f"M={a.m} seed={a.seed}: |D|={len(D)} max|hat D(r)|={mx:.4f} threshold={thresh:.4f} ok={ok}")
    print("D =", D)
    # verify convolution at 0 explicitly
    conv0 = sum(1 for x in D if (-x) % a.m in set(D))
    print("(1_D*1_D)(0) =", conv0, "(must be 0)")

if __name__ == "__main__":
    main()

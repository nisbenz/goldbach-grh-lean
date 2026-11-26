#!/usr/bin/env python3
"""
Deterministic Pratt-certificate prime ladder generator & independent verifier.

Given:
  - B: verified binary Goldbach upper bound (e.g., B = 4 * 10^18 from
       Oliveira e Silva, Herzog, Pardi (2014), Math. Comp. 83(288), 2033-2060),
  - N0: analytic threshold from the GRH Weak Goldbach proof,

this script builds a prime ladder p_0 < p_1 < ... < p_k such that:
  1. p_0 <= B - 4 (odd prime),
  2. p_{i+1} - p_i <= B - 4 for all 0 <= i < k,
  3. p_k >= N0 - 4,
  4. EVERY prime p_i has a complete, recursively verified Pratt primality certificate
     (Lucas converse of Fermat's Little Theorem: witness g such that
      g^(p-1) == 1 (mod p) and g^((p-1)/q) != 1 (mod p) for every prime factor q of p-1,
      with recursive certificates for all prime factors q > 2).

Therefore, for every odd N in [B + 1, N0], taking the largest p_i <= N - 4 yields
an even integer E = N - p_i in [4, B], which is a sum of two primes q + r, so
N = p_i + q + r.
"""

import json
import math
import random
import sys
from pathlib import Path


def is_probable_prime(n: int) -> bool:
    if n < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for p in small:
        if n == p:
            return True
        if n % p == 0:
            return False
    d = n - 1
    s = 0
    while (d & 1) == 0:
        d >>= 1
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if a >= n:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


def pollard_rho(n: int) -> int:
    if n % 2 == 0:
        return 2
    if n % 3 == 0:
        return 3
    rng = random.Random(1337 ^ n)
    while True:
        c = rng.randrange(1, n)
        x = rng.randrange(2, n)
        y = x
        d = 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = math.gcd(abs(x - y), n)
        if d != n:
            return d


def factorize(n: int) -> dict[int, int]:
    factors: dict[int, int] = {}
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47):
        while n % p == 0:
            factors[p] = factors.get(p, 0) + 1
            n //= p
    stack = [n] if n > 1 else []
    while stack:
        m = stack.pop()
        if m == 1:
            continue
        if is_probable_prime(m):
            factors[m] = factors.get(m, 0) + 1
        else:
            d = pollard_rho(m)
            stack.append(d)
            stack.append(m // d)
    return factors


def build_pratt_cert(p: int, cache: dict[int, dict]) -> dict:
    """Build a complete Pratt primality certificate for prime p."""
    if p == 2:
        return {"p": 2}
    if p in cache:
        return cache[p]
    fac = factorize(p - 1)
    distinct_qs = sorted(fac.keys())
    # Find primitive root (or Lucas witness) g
    g = 2
    while True:
        if pow(g, p - 1, p) == 1 and all(pow(g, (p - 1) // q, p) != 1 for q in distinct_qs):
            break
        g += 1
    subcerts = {str(q): build_pratt_cert(q, cache) for q in distinct_qs if q > 2}
    cert = {
        "p": p,
        "g": g,
        "factors": {str(q): e for q, e in sorted(fac.items())},
        "subcerts": subcerts,
    }
    cache[p] = cert
    return cert


def verify_pratt_cert(cert: dict, verified: set[int]) -> bool:
    """Independently verify a Pratt certificate from first principles (no probabilistic tests)."""
    p = cert["p"]
    if p == 2:
        verified.add(2)
        return True
    if p in verified:
        return True
    if p < 2 or (p & 1) == 0:
        return False
    g = cert["g"]
    factors = {int(k): int(v) for k, v in cert["factors"].items()}
    # 1. Check product of q^e == p - 1
    prod = 1
    for q, e in factors.items():
        if e <= 0:
            return False
        prod *= q ** e
    if prod != p - 1:
        return False
    # 2. Check Fermat condition g^(p-1) == 1 (mod p)
    if pow(g, p - 1, p) != 1:
        return False
    # 3. Check g^((p-1)/q) != 1 (mod p) and recursively verify each q
    subcerts = cert.get("subcerts", {})
    for q in factors:
        if pow(g, (p - 1) // q, p) == 1:
            return False
        if q != 2:
            if str(q) not in subcerts:
                return False
            if subcerts[str(q)]["p"] != q:
                return False
            if not verify_pratt_cert(subcerts[str(q)], verified):
                return False
    verified.add(p)
    return True


def prev_prime(x: int) -> int:
    cand = x if (x & 1) else x - 1
    while cand >= 3:
        if is_probable_prime(cand):
            return cand
        cand -= 2
    raise ValueError("No prime found")


def build_and_verify_ladder(B: int, N0: int, out_path: Path | None = None) -> None:
    max_step = B - 4
    if N0 <= B + 3:
        print(f"N0 = {N0} <= B + 3 = {B + 3}: no ladder needed beyond binary Goldbach bound B!")
        return

    cache: dict[int, dict] = {}
    primes: list[int] = []
    certs: list[dict] = []

    p0 = prev_prime(max_step)
    primes.append(p0)
    certs.append(build_pratt_cert(p0, cache))

    cur = p0
    while cur < N0 - 4:
        nxt = prev_prime(cur + max_step)
        assert nxt > cur and nxt - cur <= max_step
        primes.append(nxt)
        certs.append(build_pratt_cert(nxt, cache))
        cur = nxt

    # Independent verification pass
    verified: set[int] = set()
    assert primes[0] <= max_step and (primes[0] & 1) == 1
    assert primes[-1] >= N0 - 4
    max_gap = 0
    for i, (p, cert) in enumerate(zip(primes, certs)):
        assert cert["p"] == p
        assert verify_pratt_cert(cert, verified), f"Pratt verification failed for {p}"
        if i > 0:
            gap = p - primes[i - 1]
            assert 0 < gap <= max_step, f"Gap {gap} exceeds {max_step}"
            max_gap = max(max_gap, gap)

    print(f"PASS: Built & independently verified Pratt-certified prime ladder!")
    print(f"  Binary Goldbach base B = {B:,}")
    print(f"  Target threshold N0    = {N0:,}")
    print(f"  Ladder rungs           = {len(primes)}")
    print(f"  p_0                    = {primes[0]:,} (<= B - 4)")
    print(f"  p_last                 = {primes[-1]:,} (>= N0 - 4)")
    print(f"  Max consecutive gap    = {max_gap:,} (<= B - 4 = {max_step:,})")
    print(f"  Total unique primes certified via Pratt trees: {len(verified)}")

    if out_path is not None:
        out_path.write_text(json.dumps({
            "B": B,
            "N0": N0,
            "max_step": max_step,
            "rungs": len(primes),
            "primes": primes,
            "certificates": certs,
        }, indent=2))
        print(f"  Saved certificates to {out_path}")


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print("Usage: verify_ladder.py <B> <N0> [out.json]")
        sys.exit(2)
    B_arg = int(float(sys.argv[1])) if ("e" in sys.argv[1].lower()) else int(sys.argv[1])
    N0_arg = int(float(sys.argv[2])) if ("e" in sys.argv[2].lower()) else int(sys.argv[2])
    out_arg = Path(sys.argv[3]) if len(sys.argv) >= 4 else None
    build_and_verify_ladder(B_arg, N0_arg, out_arg)

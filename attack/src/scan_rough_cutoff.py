"""Compare both marks in ERH report (8) at two cutoffs for every even N <= 200000."""
from math import exp, isqrt, log

import numpy as np


def cutoff_wall(prime, numerator, denominator, limit):
    """First N >= 4 such that prime <= N^(numerator/denominator)."""
    power = prime**denominator
    low, high = 4, limit + 1
    while low < high:
        mid = (low + high) // 2
        if mid**numerator >= power:
            high = mid
        else:
            low = mid + 1
    return low


def scan(limit, numerator, denominator, integers, primes, least, liouville, log_prime):
    small = []
    walls = {4, limit + 1}
    for prime in primes:
        if prime**3 > limit and prime**denominator > limit**numerator:
            break
        wall = cutoff_wall(prime, numerator, denominator, limit)
        small.append((prime, wall))
        walls.update((wall, min(limit + 1, max(4, prime**3))))

    ratios = np.zeros((2, limit + 1))
    for low, stop in zip(sorted(walls), sorted(walls)[1:]):
        targets = integers[low + low % 2 : stop : 2]
        if not len(targets):
            continue
        cut = [p for p, wall in small if wall <= low]
        rough = (least[:stop] > max(cut, default=1)) & (integers[:stop] > 1)
        mark = np.zeros(stop, dtype=int)
        for p, wall in small:
            if wall > low and p**3 <= low:
                mark[p::p] += 1
        density = np.ones(len(targets))
        for p in cut:
            density[targets % p != 0] *= 1 - 1 / (p - 1)

        size = 1 << (2 * stop - 2).bit_length()
        spectrum = np.fft.rfft(log_prime[:stop], size)
        sign = liouville[:stop]
        weights = (rough * (sign + (1 - sign) * mark),
                   rough * (1 - 2 * (log_prime[:stop] > 0)))
        for row, weight in enumerate(weights):
            values = np.fft.irfft(spectrum * np.fft.rfft(weight, size), size)[targets]
            for p in primes:
                if 2 * p >= stop:
                    break
                # Remove exactly the terms with p | N among these even targets.
                start, step = (0, 1) if p == 2 else ((-int(targets[0]) // 2) % p, p)
                values[start::step] -= log_prime[p] * weight[targets[start::step] - p]
            ratios[row, targets] = values / (targets * density)

    s = denominator / (2 * numerator)
    threshold = 2 * exp(np.euler_gamma) * log(s - 1) / s
    even = integers[4::2]
    late = even[even >= 100000]
    for name, ratio in zip(("original", "capped"), ratios):
        peak = late[ratio[late].argmax()]
        print(numerator, denominator, name, "threshold", threshold,
              "crossings", even[ratio[even] >= threshold].tolist(),
              "late maximum", int(peak), ratio[peak],
              "samples", ratio[[10000, 100000, 200000]].tolist())


if __name__ == "__main__":
    limit = 200000
    integers = np.arange(limit + 1)
    least = integers.copy()
    for p in range(2, isqrt(limit) + 1):
        if least[p] == p:
            multiples = least[p*p::p]
            np.minimum(multiples, p, out=multiples)
    prime_mask = (integers > 1) & (integers == least)
    primes = integers[prime_mask].tolist()
    log_prime = np.zeros(limit + 1)
    log_prime[prime_mask] = np.log(integers[prime_mask])
    liouville = np.ones(limit + 1, dtype=np.int8)
    for n in range(2, limit + 1):
        liouville[n] = -liouville[n // least[n]]
    for numerator, denominator in ((201, 1000), (2, 9)):
        scan(limit, numerator, denominator, integers, primes, least, liouville, log_prime)

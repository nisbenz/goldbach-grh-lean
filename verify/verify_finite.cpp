// Independent computational verifier for the Weak (Ternary) Goldbach Conjecture.
//
// Part 1: Sieves all primes up to M (default 10^9) and verifies directly that
//         every even integer E in [4, M] is a sum of two primes E = p + q.
//         This immediately certifies Weak Goldbach for every odd N in [7, M + 3]
//         via N = 3 + p + q (since N - 3 is even in [4, M]).
//
// Part 2: Extends the certification up to a target L <= 2^63 - 1 using a
//         verified prime ladder p_0 < p_1 < ... < p_k with:
//           - p_0 <= M - 4,
//           - p_{i+1} - p_i <= M - 4 for all i,
//           - p_k >= L - 4.
//         For every odd N in [M + 5, L], letting p_i be the largest ladder prime
//         <= N - 4, the difference E = N - p_i is even and satisfies 4 <= E <= M,
//         hence E = q + r by Part 1, so N = p_i + q + r.
//         Each ladder prime p_i < 2^64 is proved prime using the deterministic
//         7-base Miller-Rabin theorem (Sinclair 2011; exact for all n < 2^64).

#include <algorithm>
#include <atomic>
#include <cerrno>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <mutex>
#include <thread>
#include <vector>

namespace {

using u64 = uint64_t;
using u128 = unsigned __int128;

bool parse_bound(const char* text, u64& value) {
    if (*text < '0' || *text > '9') return false;
    char* end = nullptr;
    errno = 0;
    const auto parsed = std::strtoull(text, &end, 10);
    if (errno != 0 || *end != '\0' || parsed > std::numeric_limits<u64>::max()) return false;
    value = static_cast<u64>(parsed);
    return true;
}

u64 mul_mod(u64 a, u64 b, u64 mod) {
    return static_cast<u64>((static_cast<u128>(a) * b) % mod);
}

u64 pow_mod(u64 base, u64 exp, u64 mod) {
    u64 res = 1;
    base %= mod;
    while (exp > 0) {
        if (exp & 1) res = mul_mod(res, base, mod);
        base = mul_mod(base, base, mod);
        exp >>= 1;
    }
    return res;
}

// Deterministic primality test for all 64-bit unsigned integers (n < 2^64).
// Proven exact using Jim Sinclair's 7-base set (2011).
bool is_prime_u64(u64 n) {
    if (n < 2) return false;
    static constexpr u64 small_primes[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
    for (u64 p : small_primes) {
        if (n == p) return true;
        if (n % p == 0) return false;
    }
    u64 d = n - 1;
    int s = 0;
    while ((d & 1) == 0) {
        d >>= 1;
        ++s;
    }
    static constexpr u64 bases[] = {
        2ULL, 325ULL, 9375ULL, 28178ULL, 450775ULL, 9780504ULL, 1795265022ULL
    };
    for (u64 a : bases) {
        if (a % n == 0) continue;
        u64 x = pow_mod(a, d, n);
        if (x == 1 || x == n - 1) continue;
        bool composite = true;
        for (int r = 1; r < s; ++r) {
            x = mul_mod(x, x, n);
            if (x == n - 1) {
                composite = false;
                break;
            }
        }
        if (composite) return false;
    }
    return true;
}

// Bitset storing odd numbers only: bit k represents 2*k + 1.
// Bit = 0 means prime, Bit = 1 means composite.
struct OddSieve {
    u64 limit;
    std::vector<uint64_t> comp;

    explicit OddSieve(u64 max_n) : limit(max_n) {
        u64 num_odds = (max_n / 2) + 1;
        comp.assign((num_odds + 63) / 64, 0ULL);
        set_comp(0); // 1 is not prime
        for (u64 i = 3; i * i <= max_n; i += 2) {
            if (!is_comp(i >> 1)) {
                u64 step = i;
                for (u64 j = (i * i) >> 1; j < num_odds; j += step) {
                    set_comp(j);
                }
            }
        }
    }

    inline void set_comp(u64 idx) { comp[idx >> 6] |= (1ULL << (idx & 63)); }
    inline bool is_comp(u64 idx) const { return (comp[idx >> 6] >> (idx & 63)) & 1ULL; }
    inline bool is_prime(u64 n) const {
        if (n < 2) return false;
        if (n == 2) return true;
        if ((n & 1) == 0) return false;
        return !is_comp(n >> 1);
    }
};

} // namespace

int main(int argc, char** argv) {
    u64 M = 1'000'000'000ULL;      // Binary Goldbach direct verification bound
    u64 L = 1'000'000'000'000ULL;  // Local prime-ladder Weak Goldbach bound (10^12)
    constexpr u64 max_bound = (1ULL << 63) - 1;
    if (argc > 3 || (argc >= 2 && !parse_bound(argv[1], M)) ||
        (argc >= 3 && !parse_bound(argv[2], L)) || M < 4 || M > max_bound || L > max_bound) {
        std::cerr << "Usage: verify_finite [M [L]], with 4 <= M <= 2^63-1 and 0 <= L <= 2^63-1\n";
        return 2;
    }
    if ((M & 1) != 0) ++M;
    if (L > M + 3 && M < 8) {
        std::cerr << "ERROR: The ladder requires an odd prime <= M - 4 (even M >= 8).\n";
        return 2;
    }

    std::cout << "[1/3] Sieving primes up to M = " << M << "...\n" << std::flush;
    OddSieve sieve(M);

    // Collect odd primes up to 100000 for fast inner loop (max minimal Goldbach prime
    // up to 10^9 is < 2000; fallback scans full sieve if needed).
    std::vector<u64> small_odd_primes;
    u64 small_cap = std::min<u64>(M, 200'000ULL);
    for (u64 p = 3; p <= small_cap; p += 2) {
        if (sieve.is_prime(p)) small_odd_primes.push_back(p);
    }

    std::cout << "[2/3] Verifying binary Goldbach for all even E in [4, " << M << "]...\n" << std::flush;
    // E = 4 = 2 + 2; for all even E >= 6, find odd prime p <= E/2 such that E - p is prime.
    unsigned num_threads = std::max(1u, std::thread::hardware_concurrency());
    std::atomic<bool> failed{false};
    std::atomic<u64> max_min_prime{2};
    std::atomic<u64> total_even_checked{1}; // counting E = 4
    std::mutex err_mtx;

    u64 chunk = 2'000'000ULL; // even chunk size
    std::atomic<u64> next_start{6};

    auto worker = [&]() {
        u64 local_max_p = 2;
        u64 local_count = 0;
        while (!failed.load(std::memory_order_relaxed)) {
            u64 start = next_start.fetch_add(chunk, std::memory_order_relaxed);
            if (start > M) break;
            u64 end = std::min(M, start + chunk - 2);
            for (u64 E = start; E <= end; E += 2) {
                bool ok = false;
                u64 found_p = 0;
                for (u64 p : small_odd_primes) {
                    if (p > E / 2) break;
                    if (sieve.is_prime(E - p)) {
                        ok = true;
                        found_p = p;
                        break;
                    }
                }
                if (!ok) {
                    for (u64 p = small_cap + 1; p <= E / 2; p += 2) {
                        if (sieve.is_prime(p) && sieve.is_prime(E - p)) {
                            ok = true;
                            found_p = p;
                            break;
                        }
                    }
                }
                if (!ok) {
                    failed.store(true, std::memory_order_relaxed);
                    std::lock_guard<std::mutex> lk(err_mtx);
                    std::cerr << "COUNTEREXAMPLE TO BINARY GOLDBACH AT E = " << E << "\n";
                    return;
                }
                if (found_p > local_max_p) local_max_p = found_p;
                ++local_count;
            }
        }
        total_even_checked.fetch_add(local_count, std::memory_order_relaxed);
        u64 prev = max_min_prime.load(std::memory_order_relaxed);
        while (local_max_p > prev && !max_min_prime.compare_exchange_weak(prev, local_max_p)) {}
    };

    std::vector<std::thread> threads;
    threads.reserve(num_threads);
    for (unsigned t = 0; t < num_threads; ++t) threads.emplace_back(worker);
    for (auto& th : threads) th.join();

    if (failed.load()) return 1;
    if (total_even_checked.load() != M / 2 - 1) {
        std::cerr << "ERROR: Incomplete binary verification count.\n";
        return 2;
    }
    std::cout << "  PASS: Checked " << total_even_checked.load()
              << " even integers in [4, " << M << "] (max minimal prime = "
              << max_min_prime.load() << ").\n"
              << "  => Weak Goldbach verified for all odd N in [7, " << (M + 3) << "].\n"
              << std::flush;

    if (L > M + 3) {
        std::cout << "[3/3] Building deterministic prime ladder up to L = " << L
                  << " (max step = " << (M - 4) << ")...\n" << std::flush;
        u64 max_step = M - 4;
        // Start p_0 = largest odd prime <= M - 4
        u64 cur = (max_step % 2 == 0) ? (max_step - 1) : max_step;
        while (cur >= 3 && !is_prime_u64(cur)) cur -= 2;
        if (cur < 3 || cur > max_step) {
            std::cerr << "ERROR: Invalid first ladder prime.\n";
            return 2;
        }
        const u64 first = cur;
        u64 rungs = 1;
        u64 max_gap_seen = 0;
        while (cur < L - 4) {
            if (max_step > std::numeric_limits<u64>::max() - cur) {
                std::cerr << "ERROR: Ladder step exceeds the 64-bit range.\n";
                return 2;
            }
            u64 target = cur + max_step;
            u64 cand = (target % 2 == 0) ? (target - 1) : target;
            while (cand > cur && !is_prime_u64(cand)) cand -= 2;
            if (cand <= cur) {
                std::cerr << "ERROR: Failed to find next ladder prime after " << cur << "\n";
                return 2;
            }
            u64 gap = cand - cur;
            if (gap > max_gap_seen) max_gap_seen = gap;
            cur = cand;
            ++rungs;
        }
        std::cout << "  PASS: Verified " << rungs << " ladder primes from p_0 = " << first << " <= " << max_step
                  << " up to p_k = " << cur << " >= " << (L - 4)
                  << " (max gap = " << max_gap_seen << " <= " << max_step << ").\n"
                  << "  => Weak Goldbach unconditionally verified on this machine for ALL odd N in [7, "
                  << L << "].\n";
    }
    return 0;
}

# H1 rational major-arc certificate — independent check (2026-11-26)

Source: `goldbach-grh-lean/proof/strong_goldbach_research.md`, lines 52–68 (Theorem 1 / H1
supporting certificate). This is a **finite rational computation**, not an analytic theorem.

## What was checked

Recomputed the midpoint/Taylor rational certificate independently in Python `fractions`:
- T = 17/4, k = 4096 midpoints, scale = 10^11
- cos Taylor degree 26 (m=0..13), sin Taylor degree 25 (m=0..12), h = u²
- f(u) = ((1-h)·a + 2h·b)/(1+h)² where a≈cos(u)/√?, b≈sin(u)/√? (as in the repo)
- total = Σ floor(scale·f) over midpoints

Result:
```
total = 115733641602738  (asserted: 115733641602738) — MATCH
2*lower/(355/113) = 0.7644831688828727 > 0.764483  — TRUE, margin ≈ 1.69e-7
```
where `lower = T·total/(k·scale) − 2·T·T^27/27! − 11·T^3/(24·k^2)`.

Command actually run: `python3 /tmp/opencode/check_h1_cert.py` (script content reproduced in
the repo doc; exit 0, output above).

## What this establishes and what it does not

- ESTABLISHED: the rational inequality `2J(T) > 0.764483` used in the repo's Theorem 1 (H1
  criterion) is correct as a finite computation. This is the independently checkable core of the
  major-arc lower bound.
- NOT ESTABLISHED: (H1) itself, `F_N(T\A) ≥ -0.764480 N`, for any even N. That is an analytic
  hypothesis about the signed minor-arc coefficient, and is the actual blocker B-002.
- This does not use GRH/ERH; it is unconditional finite arithmetic.

## Status for the map

Claim `GB-H1-CERT` → `checked` (finite computation). B-002 remains `open`.

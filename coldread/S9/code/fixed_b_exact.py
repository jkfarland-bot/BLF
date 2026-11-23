"""Exact test: with a FIXED slot width b, can one step of an elementary rule g be read as a bit of
E(x) M at a cell j whose window is not wrapped (N >= 3, 1 <= j <= N-2)?

With the other cells fixed, bit e of E(x) M is floor(u0 + beta (z0 + 2^b z1 + 2^(2b) z2)) mod 2, where
beta = 2^(pi + b(j-1)) M / 2^e and u0 is a real constant (pi only rescales beta). So a necessary condition
is that g(z0, z1, z2) = floor(u0 + beta n(z)) mod 2 with n(z) = z0 + 2^b z1 + 2^(2b) z2 for some reals u0, beta.
We decide this exactly: beta can be taken in [0, 2) and u0 in [0, 2) (both periods preserve parity);
the combinatorial type changes only at beta = k / d with d a difference of two values of n(z), and for a
fixed beta the type in u0 changes only at u0 = k - beta n. Testing midpoints decides feasibility.
If infeasible, Proposition 9.4 read with a fixed encoding of slot width b fails for g at every N >= 3.
"""
import sys
from fractions import Fraction
from itertools import product


def feasible(rule, b):
    S = []
    for z0, z1, z2 in product((0, 1), repeat=3):
        n = z0 + (z1 << b) + (z2 << (2 * b))
        S.append((n, (rule >> (4 * z0 + 2 * z1 + z2)) & 1))
    ns = [n for n, _ in S]
    diffs = sorted({abs(p - q) for p in ns for q in ns if p != q})
    bps = {Fraction(0), Fraction(2)}
    for d in diffs:
        for k in range(0, 2 * d + 1):
            bps.add(Fraction(k, d))
    bps = sorted(bps)
    for lo, hi in zip(bps, bps[1:]):
        beta = (lo + hi) / 2
        ubps = {Fraction(0), Fraction(2)}
        for n in ns:
            bn = beta * n
            for k in range(bn.__floor__(), (bn + 2).__floor__() + 1):
                u = k - bn
                if 0 <= u <= 2:
                    ubps.add(u)
        ubps = sorted(ubps)
        for ulo, uhi in zip(ubps, ubps[1:]):
            u0 = (ulo + uhi) / 2
            if all(((u0 + beta * n).__floor__() % 2) == v for n, v in S):
                return (u0, beta)
    return None


if __name__ == "__main__":
    bs = [int(a) for a in sys.argv[1:]] or [2, 3, 4]
    from blf_small import blf_representations
    blf = set(blf_representations(3, 3))
    for b in bs:
        print(f"b={b}: rule 110 realizable at an unwrapped cell: {feasible(110, b)}", flush=True)
    for b in bs:
        bad = [R for R in range(256) if R in blf and feasible(R, b) is None]
        print(f"b={b}: BLF elementary rules NOT realizable at an unwrapped cell with slot width b: "
              f"{len(bad)}; includes 110: {110 in bad}; first few: {bad[:12]}", flush=True)

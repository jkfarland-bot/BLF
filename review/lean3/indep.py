#!/usr/bin/env python3
"""Independent checks for the BLF formalization audit (verifier's own code, not from the repo).

Exact BLF test used here (derived independently from the floor characterization):
f is BLF iff f(x) = floor(u(x)) mod 2 for a real affine u.  Given such u, put m_l = floor(r_l),
beta_l = m_l mod 2 and H = floor(u) - m.x.  Then along every edge H rises by
D_l(x) = f(x) xor f(x+e_l) xor beta_l in {0,1}.  Conversely if for some beta the edge rises D_l
are path independent (square condition) and the resulting H (H(0) = f(0)) is the floor of a real
affine v, then floor(v + beta.x) has parity f.  So: f is BLF iff some beta in {0,1}^n gives a
consistent H that is a floor of an affine function; the last part is an LP (maximize eps with
H <= v <= H + 1 - eps).
"""
import itertools
import sys
from fractions import Fraction

import numpy as np
from scipy.optimize import linprog


def bits(i, n):
    return tuple((i >> k) & 1 for k in range(n))


def build_H(f, n, beta):
    """Return H as a dict over vertices (as ints) or None if the square condition fails."""
    H = {0: f[0]}
    # BFS by popcount; for each vertex check all incoming edges agree
    order = sorted(range(1 << n), key=lambda v: bin(v).count("1"))
    for v in order:
        if v == 0:
            continue
        val = None
        for l in range(n):
            if (v >> l) & 1:
                p = v ^ (1 << l)
                d = f[p] ^ f[v] ^ beta[l]
                cand = H[p] + d
                if val is None:
                    val = cand
                elif val != cand:
                    return None
        H[v] = val
    return H


def is_floor_of_affine(H, n):
    """LP: maximize eps s.t. H(x) <= t + r.x and t + r.x + eps <= H(x) + 1.  Return max eps."""
    # variables: t, r_0..r_{n-1}, eps ; minimize -eps
    A = []
    b = []
    for v in range(1 << n):
        x = bits(v, n)
        # -(t + r.x) <= -H
        A.append([-1.0] + [-float(xi) for xi in x] + [0.0])
        b.append(-float(H[v]))
        # t + r.x + eps <= H + 1
        A.append([1.0] + [float(xi) for xi in x] + [1.0])
        b.append(float(H[v]) + 1.0)
    c = [0.0] * (n + 1) + [-1.0]
    bounds = [(None, None)] * (n + 1) + [(None, 1.0)]
    res = linprog(c, A_ub=np.array(A), b_ub=np.array(b), bounds=bounds, method="highs")
    if res.status != 0:
        return None
    return -res.fun


def is_blf_exact(f, n, tol=1e-9):
    best = None
    for beta in itertools.product((0, 1), repeat=n):
        H = build_H(f, n, beta)
        if H is None:
            continue
        eps = is_floor_of_affine(H, n)
        if eps is not None and eps > tol:
            if eps < 1e-6:
                print("WARNING: tiny eps", eps, f, beta, file=sys.stderr)
            return True
        if eps is not None and best is None:
            best = eps
    return False


def square_ok_some_beta(f, n):
    return any(build_H(f, n, beta) is not None for beta in itertools.product((0, 1), repeat=n))


def truth_table(fun, n):
    return tuple(int(bool(fun(bits(v, n)))) for v in range(1 << n))


def affine_xors(n):
    out = []
    for c in (0, 1):
        for b in itertools.product((0, 1), repeat=n):
            out.append(tuple((c + sum(bi * xi for bi, xi in zip(b, bits(v, n)))) % 2 for v in range(1 << n)))
    return out


def count_blf(n, use_orbits=True):
    N = 1 << n
    total = 0
    if not use_orbits:
        for m in range(1 << N):
            f = tuple((m >> v) & 1 for v in range(N))
            total += is_blf_exact(f, n)
        return total
    aff = affine_xors(n)
    seen = set()
    for m in range(1 << N):
        if m in seen:
            continue
        f = tuple((m >> v) & 1 for v in range(N))
        orbit = set()
        for g in aff:
            h = sum(((fi ^ gi) << v) for v, (fi, gi) in enumerate(zip(f, g)))
            orbit.add(h)
        seen |= orbit
        assert len(orbit) == len(aff)
        if is_blf_exact(f, n):
            total += len(orbit)
    return total


# ---------- Rule 110 ----------
def rule(R, l, c, r):
    return (R >> (4 * l + 2 * c + r)) & 1


def r110(l, c, r):
    # Rule 110 written out from its standard table, independent of the bit formula:
    table = {(1, 1, 1): 0, (1, 1, 0): 1, (1, 0, 1): 1, (1, 0, 0): 0,
             (0, 1, 1): 1, (0, 1, 0): 1, (0, 0, 1): 1, (0, 0, 0): 0}
    return table[(l, c, r)]


def step(cells, f=r110):
    """One step on a finite window: output has len-2 cells."""
    return [f(cells[i], cells[i + 1], cells[i + 2]) for i in range(len(cells) - 2)]


def steps(cells, k, f=r110):
    for _ in range(k):
        cells = step(cells, f)
    return cells


def main():
    out = []
    # Rule 110 table vs Wolfram bit formula
    for l, c, r in itertools.product((0, 1), repeat=3):
        assert rule(110, l, c, r) == r110(l, c, r)
    out.append("eca formula bit(4l+2c+r) of 110 matches the standard Rule 110 table on all 8 patterns")

    one = truth_table(lambda x: r110(*x), 3)
    two = truth_table(lambda x: steps(list(x), 2)[0], 5)
    three = truth_table(lambda x: steps(list(x), 3)[0], 7)
    out.append("rule110 one step tt (index = sum x_i 2^i, x_0 leftmost): " + "".join(map(str, one)))
    out.append("rule110Two tt: " + "".join(map(str, two)))
    out.append("rule110Three tt: " + "".join(map(str, three)))
    with open("/home/claude/vscratch3/r110_tt_python.txt", "w") as fh:
        fh.write("".join(map(str, two)) + "\n" + "".join(map(str, three)) + "\n")

    out.append("rule110 one step BLF (exact test): %s" % is_blf_exact(one, 3))
    out.append("rule110Two square condition holds for some beta: %s" % square_ok_some_beta(two, 5))
    out.append("rule110Two BLF (exact test): %s" % is_blf_exact(two, 5))
    out.append("rule110Three square condition holds for some beta: %s" % square_ok_some_beta(three, 7))
    out.append("rule110Three BLF (exact test): %s" % is_blf_exact(three, 7))

    # The specific squares used in BLF/Rule110.lean, under the verifier's own reading of sqOk.
    def sq(f, n, i, k, p):
        pi = p | (1 << i); pk = p | (1 << k); pik = p | (1 << i) | (1 << k)
        res = []
        for bi, bk in itertools.product((0, 1), repeat=2):
            lhs = (f[p] ^ f[pk] ^ bk) + (f[pk] ^ f[pik] ^ bi)
            rhs = (f[p] ^ f[pi] ^ bi) + (f[pi] ^ f[pik] ^ bk)
            res.append(lhs == rhs)
        return res
    s0 = sq(two, 5, 3, 4, 0); s1 = sq(two, 5, 3, 4, 0b00010)
    out.append("rule110Two squares (i,k)=(3,4) at p=0 and p=e1: ok per (bi,bk) in 00,01,10,11: %s %s; both ok for some beta: %s"
               % (s0, s1, any(a and b for a, b in zip(s0, s1))))
    t0 = sq(three, 7, 5, 6, 0); t1 = sq(three, 7, 5, 6, 0b0000100)
    out.append("rule110Three squares (i,k)=(5,6) at p=0 and p=e2: %s %s; both ok for some beta: %s"
               % (t0, t1, any(a and b for a, b in zip(t0, t1))))

    # Counts
    for n in range(1, 4):
        out.append("|BLF(%d)| exact test, all functions: %d" % (n, count_blf(n, use_orbits=False)))
    out.append("|BLF(4)| exact test, affine-XOR orbits: %d" % count_blf(4, use_orbits=True))

    # 0xfc80 gated threshold
    T = truth_table(lambda x: int(x[0] + 2 * x[1] + 2 * x[2] + 3 * x[3] >= 5), 4)
    mask = sum(b << v for v, b in enumerate(T))
    out.append("T mask = %#06x" % mask)
    # minimal sum |w| for T = [tau <= w.x]
    best = None
    R = 8
    for w in itertools.product(range(-R, R + 1), repeat=4):
        S = sum(abs(a) for a in w)
        if best is not None and S >= best:
            continue
        vals = [sum(wi * xi for wi, xi in zip(w, bits(v, 4))) for v in range(16)]
        lo = max([vals[v] for v in range(16) if not T[v]], default=-10**9)
        hi = min([vals[v] for v in range(16) if T[v]], default=10**9)
        if lo < hi:
            best = S
    out.append("min sum|w_i| over integer w in [-8,8]^4 with T = [tau <= w.x]: %d" % best)
    gated = truth_table(lambda y: int(y[4] and (y[0] + 2 * y[1] + 2 * y[2] + 3 * y[3] >= 5)), 5)
    out.append("gFC80 BLF (exact test): %s" % is_blf_exact(gated, 5))
    # witness from Gated.lean: K=7, a=(1,2,2,3,4), j=4
    ok = all(gated[v] == (((7 + sum(a * xi for a, xi in zip((1, 2, 2, 3, 4), bits(v, 5)))) >> 4) & 1)
             for v in range(32))
    out.append("gFC80 = bit 4 of 7 + x1 + 2x2 + 2x3 + 3x4 + 4z on all 32 inputs: %s" % ok)
    print("\n".join(out))


if __name__ == "__main__":
    main()

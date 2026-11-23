"""Brute-force check of the selector lemma (Lemma 8.2 of the BLF paper) and of the Rule 110 squares.

1. For every threshold function T of n <= 3 variables, the least bit j at which z AND T(x) is
   bit j of an integer affine form equals ceil(log2(W1(T)+1)), W1 = least l1 norm of integer weights.
2. The 4-variable threshold 0xfc80 has W1 = 8, and z AND T (mask 0xfc800000) is not realizable at
   bit 3 but is at bit 4.
3. The 2-step (5 inputs) and 3-step (7 inputs) tables of Rule 110 contain the square patterns
   0111 and 0100 on their last two inputs, which no BLF function can (square identity).
Only the residues of K and a_i modulo 2^(j+1) matter at bit j, so the searches are exhaustive.
"""
import itertools
import numpy as np


def realizable(nvars, j):
    """Set of truth-table masks realizable as bit j of K + a.x on nvars variables."""
    M = 1 << (j + 1)
    pts = np.array([[(x >> i) & 1 for i in range(nvars)] for x in range(1 << nvars)], dtype=np.int64)
    out = set()
    grids = np.array(list(itertools.product(range(M), repeat=nvars)), dtype=np.int64)  # a vectors
    lin = grids @ pts.T  # (#a, 2^nvars)
    weights = (1 << np.arange(1 << nvars, dtype=np.int64)) if nvars <= 5 else None
    for K in range(M):
        bits = ((K + lin) >> j) & 1
        out.update((bits * weights).sum(axis=1).tolist())
    return out


def thresholds(n, wmax):
    best = {}
    pts = [[(x >> i) & 1 for i in range(n)] for x in range(1 << n)]
    for w in itertools.product(range(-wmax, wmax + 1), repeat=n):
        s = sum(abs(v) for v in w)
        if s > wmax:
            continue
        vals = [sum(a * b for a, b in zip(w, p)) for p in pts]
        for tau in range(min(vals), max(vals) + 2):
            mask = sum(1 << x for x, v in enumerate(vals) if v >= tau)
            if mask not in best or s < best[mask]:
                best[mask] = s
    return best


def gate(n, T):  # z is the last variable
    return T << (1 << n)


for n in range(0, 4):
    th = thresholds(n, 6)
    assert len(th) == [2, 4, 14, 104][n]
    real = {j: realizable(n + 1, j) for j in range(4)}
    for T, w1 in th.items():
        j = next(j for j in range(4) if gate(n, T) in real[j])
        assert (1 << j) >= w1 + 1 and (j == 0 or (1 << (j - 1)) < w1 + 1), (n, T, w1, j)
    print(f"n={n}: {len(th)} thresholds, selector lemma holds (max W1 {max(th.values())})")

th4 = thresholds(4, 8)
assert th4[0xfc80] == 8 and max(th4.values()) == 8 and len(th4) == 1882
assert 0xfc800000 not in realizable(5, 3)
assert sum((((7 + x1 + 2 * x2 + 2 * x3 + 3 * x4 + 4 * z) >> 4) & 1) << (x1 + 2 * x2 + 4 * x3 + 8 * x4 + 16 * z)
           for x1, x2, x3, x4, z in itertools.product((0, 1), repeat=5)) == 0xfc800000
print("0xfc80: W1 = 8; z AND T first appears at bit 4")


def rule110(steps, bits):  # bits[0] is the leftmost cell
    row = list(bits)
    for _ in range(steps):
        row = [(110 >> (4 * a + 2 * b + c)) & 1 for a, b, c in zip(row, row[1:], row[2:])]
    return row[0]


def square_ok(g):  # g = (g00, g01, g10, g11): the two paths have equal 0/1 increments
    a, b, c, d = g
    return (a ^ b) + (b ^ d) == (a ^ c) + (c ^ d)


for steps in (2, 3):
    r = 2 * steps + 1
    pats = set()
    for rest in itertools.product((0, 1), repeat=r - 2):
        sq = tuple(rule110(steps, rest + (u, v)) for u in (0, 1) for v in (0, 1))
        pats.add(sq)
    assert (0, 1, 1, 1) in pats and (0, 1, 0, 0) in pats
    # for each parity pair (u, v) of the integer coefficients of the last two inputs,
    # some pattern violates the square identity after XOR with the affine part
    for u, v in itertools.product((0, 1), repeat=2):
        assert any(not square_ok(tuple(s[2 * a + b] ^ (a & u) ^ (b & v) for a in (0, 1) for b in (0, 1)))
                   for s in pats), (steps, u, v)
    print(f"Rule 110, {steps} steps ({r} inputs): not BLF")

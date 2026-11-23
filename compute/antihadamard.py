"""Independent check of the anti-Hadamard construction of Section 8 of the BLF paper.

Written from the paper's description (not from the ChatGPT checkers).  Entries are +1/-1 lists.
For a seed prime p (d = 2(p+1)), a lift level l >= 3 and a padding k >= 0 it builds the
sign matrix A of order m = d*2^l + k, then computes exactly (fraction-free Bareiss)
  det A  and  the cofactor-based entry (A^{-1})_{0,s},  s = d(1 + l + C(l,2)),
and checks |det A| = 2^(m-1) and (A^{-1})_{0,s} >= P(d,l)/r with r = d*2^l.
Usage: python3 antihadamard.py p l k
"""
import sys
from fractions import Fraction
from math import comb, prod


def seed(p):
    q, d = p + 1, 2 * (p + 1)
    sq = {a * a % p for a in range(1, p)}
    chi = lambda a: 0 if a % p == 0 else (1 if a % p in sq else -1)
    eps = chi(-1)
    # index 0 = infinity, index b+1 = field element b
    def K(a, b):
        if a == b:
            return 0
        if a == 0:
            return 1
        if b == 0:
            return eps
        return chi((a - 1) - (b - 1))
    U = ((1, 1), (1, -1))
    V = ((1, -1), (-eps, -eps))
    def row(a, i):  # row i (0 top, 1 bottom) of pair a
        out = []
        for b in range(q):
            for j in range(2):
                out.append(V[i][j] if a == b else K(a, b) * U[i][j])
        return out
    H = [row(a, 1) for a in range(q)] + [row(a, 0) for a in range(q)]
    dot = lambda x, y: sum(s * t for s, t in zip(x, y))
    assert all(dot(H[i], H[j]) == d * (i == j) for i in range(d) for j in range(d))
    D = [list(h) for h in H[:q]]
    for a in range(q):
        base = list(H[(a + 1) % q])  # bottom row of the next pair
        if a < q - 1:
            base[2 * a] *= -1
            base[2 * a + 1] *= -1
        else:
            base[2 * a] *= -1
        if dot(base, H[q + a]) < 0:
            base = [-v for v in base]
        D.append(base)
    # normalize: columns by first row of H, then rows by first column of H
    c = H[0][:]
    H = [[h[j] * c[j] for j in range(d)] for h in H]
    D = [[x[j] * c[j] for j in range(d)] for x in D]
    for i in range(d):
        if H[i][0] < 0:
            H[i] = [-v for v in H[i]]
            D[i] = [-v for v in D[i]]
    piv = [dot(D[i], H[i]) for i in range(d)]
    assert all(dot(D[i], H[j]) == 0 for i in range(d) for j in range(i + 1, d))
    assert sorted(piv) == sorted([d] * q + [4] * (q - 1) + [2]), piv
    assert all(v == 1 for v in H[0]) and all(h[0] == 1 for h in H)
    return H, D, piv


def order(l):
    def gray(k, t):  # reflected combination list of t-subsets of k elements (bitmasks)
        if t == 0:
            return [0]
        if t == k:
            return [(1 << k) - 1]
        return gray(k - 1, t) + [(1 << (k - 1)) | s for s in reversed(gray(k - 1, t - 1))]
    out = []
    for t in range(l + 1):
        layer = gray(l, t)
        out += list(reversed(layer)) if t % 2 else layer
    for R, S in zip(out, out[1:]):
        dlt = R ^ S
        assert (bin(dlt).count("1") == 1 and R & S == R) or \
               (bin(dlt).count("1") == 2 and bin(R).count("1") == bin(S).count("1"))
    return out


def build(p, l, k):
    H, D, piv = seed(p)
    d = len(H)
    subsets = order(l)
    par = lambda x: bin(x).count("1") & 1
    chi = lambda S, x: -1 if par(S & x) else 1
    cols = [(x, j) for x in range(1 << l) for j in range(d)]
    A = []
    for b, S in enumerate(subsets):
        g = [H[d - 1][j] ** b for j in range(d)] if b else [1] * d
        if b == 0:
            A += [[D[i][j] for x, j in cols] for i in range(d)]
            continue
        R = subsets[b - 1]
        common, dlt = R & S, R ^ S
        # x in W-perp: x has no element of R cap S and even overlap with R xor S
        A.append([chi(R, x) * g[j] * (1 if (x & common) == 0 and not par(x & dlt) else -1)
                  for x, j in cols])
        for i in range(1, d):
            A.append([g[j] * (D[i][j] if (S & x) == 0 else -chi(S, x) * H[i - 1][j])
                      for x, j in cols])
    r = len(A)
    if k:
        a01 = A[0][1]
        A = [row + [row[1]] * k for row in A]
        for t in range(k):
            A.append(A[0][:r] + [a01 * (1 - 2 * (u == t)) for u in range(k)])
    return A, r, d


def bareiss(M):
    M = [row[:] for row in M]
    n, sign, prev = len(M), 1, 1
    for c in range(n - 1):
        piv = next((i for i in range(c, n) if M[i][c]), None)
        if piv is None:
            return 0
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            sign = -sign
        for i in range(c + 1, n):
            for j in range(c + 1, n):
                M[i][j] = (M[c][c] * M[i][j] - M[i][c] * M[c][j]) // prev
            M[i][c] = 0
        prev = M[c][c]
    return sign * M[-1][-1]


def main():
    p, l, k = map(int, sys.argv[1:4])
    A, r, d = build(p, l, k)
    m = len(A)
    assert all(v in (1, -1) for row in A for v in row)
    det = bareiss(A)
    assert abs(det) == 1 << (m - 1), (det, m)
    s = d * (1 + l + comb(l, 2))
    minor = [row[1:] for i, row in enumerate(A) if i != s]  # delete row s and column 0
    cof = (-1) ** (s + 0) * bareiss(minor)
    inv = Fraction(cof, det)  # (A^{-1})_{0,s} = C_{s,0} / det
    Pexact = prod((Fraction(d, 4) ** (d // 2) * ((1 << t) - 4) ** d) ** comb(l, t)
                  for t in range(3, l + 1))
    assert inv >= Pexact / r, (inv, Pexact / r)
    print(f"p={p} l={l} pad={k} m={m} det=+-2^{m-1} s={s} (A^-1)_0s={inv} "
          f"bits={int(inv).bit_length()} P/r bits={int(Pexact / r).bit_length()}")


if __name__ == "__main__":
    main()

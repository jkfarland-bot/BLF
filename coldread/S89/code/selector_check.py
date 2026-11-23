"""Brute-force check of Lemma 8.2 for all threshold functions of m<=3 variables, and the 0xfc80 example."""
import itertools, math
import numpy as np

def pts(m):
    return list(itertools.product((0, 1), repeat=m))

def tt(m, w, tau):
    return tuple(int(sum(wi * xi for wi, xi in zip(w, x)) >= tau) for x in pts(m))

def thresholds_W1(m, S=12):
    W1 = {}
    for k in range(S + 1):
        for w in itertools.product(range(-k, k + 1), repeat=m):
            if sum(map(abs, w)) != k: continue
            for tau in range(-k - 1, k + 2):
                f = tt(m, w, tau)
                if f not in W1: W1[f] = k
    return W1

def least_bit(m, f, jmax):
    P = np.array(pts(m), dtype=np.int64).reshape(-1, m) if m else np.zeros((1, 0), dtype=np.int64)
    target = np.array([[0] * len(f), list(f)], dtype=np.int64)   # z=0 row, z=1 row
    for j in range(jmax + 1):
        M = 2 ** (j + 1)
        # coefficients (K, a_1..a_m, c) mod 2^{j+1}
        grids = np.array(list(itertools.product(range(M), repeat=m + 2)), dtype=np.int64)
        K = grids[:, 0:1]; a = grids[:, 1:m + 1]; c = grids[:, m + 1:m + 2]
        base = K + a @ P.T                     # shape (#coef, 2^m)
        ok = np.all(((base >> j) & 1) == target[0], axis=1) & np.all((((base + c) >> j) & 1) == target[1], axis=1)
        if ok.any():
            return j
    return None

total = 0; bad = 0
for m in range(0, 4):
    W1 = thresholds_W1(m)
    print(f"m={m}: {len(W1)} threshold functions, W1 values {sorted(set(W1.values()))}")
    for f, k in W1.items():
        pred = math.ceil(math.log2(k + 1))
        j = least_bit(m, f, pred)
        total += 1
        if j != pred:
            bad += 1; print("MISMATCH", m, f, k, j, pred)
print(f"total {total} threshold functions, mismatches {bad}")

# 0xfc80 example
m = 4
f = tt(4, (1, 2, 2, 3), 5)
idx = lambda x: sum(b << i for i, b in enumerate(x))  # x1 is least significant
val = sum(f[n] << idx(x) for n, x in enumerate(pts(4)))
print("truth table of [x1+2x2+2x3+3x4>=5] with x1 = LSB:", hex(val))
W1 = thresholds_W1(4, S=10)
print("W1 =", W1[f])
N = lambda x, z: 7 + x[0] + 2 * x[1] + 2 * x[2] + 3 * x[3] + 4 * z
print("bit 4 of 7+x1+2x2+2x3+3x4+4z equals z AND T:",
      all(((N(x, z) >> 4) & 1) == (z & f[n]) for n, x in enumerate(pts(4)) for z in (0, 1)))
# bit 3 impossible: exhaustive over residues mod 16 (16^6 combos), chunked
P = np.array(pts(4), dtype=np.int64); F = np.array(f, dtype=np.int64)
found = False
for K in range(16):
    for c in range(16):
        a = np.array(list(itertools.product(range(16), repeat=4)), dtype=np.int64)
        base = K + a @ P.T
        ok = np.all(((base >> 3) & 1) == 0, axis=1) & np.all((((base + c) >> 3) & 1) == F, axis=1)
        if ok.any(): found = True
print("realizable at bit 3:", found)

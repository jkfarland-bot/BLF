"""Direct enumeration of BLF(n) = {x -> bit j of (K + a.x)} for 0 <= K, a_i < 2^(j+1), j <= J.
Usage: python3 blf_direct.py n J
"""
import sys, itertools
import numpy as np
n = int(sys.argv[1]); J = int(sys.argv[2])
V = np.array(list(itertools.product([0, 1], repeat=n)), dtype=np.int64)
seen = set()
for j in range(J + 1):
    M = 2 ** (j + 1)
    K = np.arange(M, dtype=np.int64)
    for a in itertools.product(range(M), repeat=n):
        vals = K[:, None] + (V @ np.array(a, dtype=np.int64))[None, :]
        bits = (vals >> j) & 1
        w = bits @ (1 << np.arange(len(V), dtype=np.int64))
        seen.update(w.tolist())
    print(f"n={n} j<={j}: |BLF| so far = {len(seen)}", flush=True)

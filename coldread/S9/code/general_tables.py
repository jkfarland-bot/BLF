"""Theorem 9.5 for arbitrary local tables g (not only elementary rules), arbitrary r and offsets o
(including o < 0 and o >= N), every row of length N <= Nmax. Here y_j is evaluated from the Model:
y_j = g(x_{j-o}, ..., x_{j-o+r-1}), indices mod N."""
import random
import sys
import time
from itertools import product
from common import encode, all_rows
from thm95 import build_thm95


def main(Nmax=7, trials=40, seed=5):
    rng = random.Random(seed)
    t0 = time.time()
    count = 0
    for r in (1, 2, 3, 4, 5):
        for tr in range(trials):
            p = rng.choice([0.0, 0.1, 0.5, 0.9, 1.0])
            g = {m: int(rng.random() < p) for m in product((0, 1), repeat=r)}
            o = rng.randint(-3, r + 9)
            for N in range(1, Nmax + 1):
                b, pi, M, A, D, info = build_thm95(g, r, o, N)
                for x in all_rows(N):
                    y = tuple(g[tuple(x[(j - o + d) % N] for d in range(r))] for j in range(N))
                    if encode(y, b, pi) != ((encode(x, b, pi) * M) & A) % D:
                        print("FAIL", r, o, N, x, g)
                        return
                    count += 1
    print(f"general tables: OK on {count} rows (r = 1..5, {trials} random tables each, "
          f"random o in [-3, r+9], N <= {Nmax}); {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main(*(int(a) for a in sys.argv[1:]))

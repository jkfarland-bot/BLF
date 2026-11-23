"""Probe for the statement of Proposition 9.4, which writes E(x) without saying that b and pi are chosen.
For a FIXED small encoding (b, pi), search multipliers M < 2^Mbits for which every y_j (one step of an
elementary rule) is some bit of E(x) M on all rows of N cells. A failure is not a proof that no M exists,
only evidence that the quantifier 'for suitable b, pi' matters."""
import sys
from itertools import product
from common import encode, eca_step


def probe(rule, N, b, pi, Mbits):
    rows = list(product((0, 1), repeat=N))
    targets = []
    for j in range(N):
        t = 0
        for idx, x in enumerate(rows):
            t |= eca_step(rule, x)[j] << idx
        targets.append(t)
    Es = [encode(x, b, pi) for x in rows]
    found = []
    for M in range(1, 1 << Mbits):
        P = [E * M for E in Es]
        width = max(p.bit_length() for p in P)
        cols = set()
        for e in range(width):
            col = 0
            for idx, p in enumerate(P):
                col |= ((p >> e) & 1) << idx
            cols.add(col)
        if all(t in cols for t in targets):
            found.append(M)
            if len(found) >= 3:
                break
    return found


if __name__ == "__main__":
    Mbits = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    for rule in (160, 110, 232):
        for (b, pi) in ((3, 1), (4, 2)):
            for N in (4, 5):
                f = probe(rule, N, b, pi, Mbits)
                print(f"rule {rule}, b={b}, pi={pi}, N={N}: M < 2^{Mbits} that work: {f if f else 'none'}")

"""Theorem 9.5 and Proposition 9.4: build M, A, D exactly as the proof describes,
and check against direct cyclic simulation (not against the table g on wrapped windows).

Usage:
  python3 thm95.py thm   [Nmax]      all 256 rules, k = 1, 2, 3, every row of length N <= Nmax
  python3 thm95.py prop  [Nmax]      Prop 9.4 for the BLF elementary rules, k = 1
  python3 thm95.py big   [trials]    Rule 110, k = 3, random rows of 256 cells
"""
import sys
import random
import time
from itertools import product
from common import encode, eca_steps, eca_table, all_rows
from blf_small import blf_representations


def ceil_div(a, b):
    return -((-a) // b)


def choose_pi(ell, r):
    """least pi > ell with 2^pi > 2^(ell+1) (r+1)."""
    pi = ell + 1
    while not (1 << pi) > (1 << (ell + 1)) * (r + 1):
        pi += 1
    return pi


def block_mult(t, c, K, pi, b, r):
    """2^t ( sum_d c_d 2^(b(r-d)) + 2^pi K 2^(b r) )."""
    s = 0
    for d in range(r):
        s += c[d] << (b * (r - d))
    s += (K << pi) << (b * r)
    return s << t


class Layout:
    def __init__(self, r, N, ell):
        self.r, self.N, self.ell = r, N, ell
        self.pi = choose_pi(ell, r)
        self.b = 2 * self.pi + ell + 3
        self.P = ceil_div(r - 1, N) + 1
        self.rep = sum(1 << (self.b * N * q) for q in range(self.P))
        self.beta = self.b * (r + self.P * N + 1)
        bN = self.b * N
        # bN * ceil(beta/(bN) + 1) = bN * (ceil(beta/(bN)) + 1)
        self.spacing = bN * (ceil_div(self.beta, bN) + 1)


def build_thm95(g, r, o, N):
    """g: dict tuple->bit on {0,1}^r. Returns (b, pi, M, A, D, info)."""
    L = 0
    while not (1 << L) > r:
        L += 1
    lay = Layout(r, N, L)
    b, pi, bN = lay.b, lay.pi, lay.b * N
    mod = 1 << (L + 1)
    blocks_sum = 0
    A = 0
    k = 0
    offsets = []
    for m in product((0, 1), repeat=r):
        if not g[m]:
            continue
        K = (1 << L) - sum(m)
        c = [(2 * md - 1) % mod for md in m]
        assert 0 <= K < mod and all(0 <= cd < mod for cd in c)
        # extracted bit of cell i: t + b(r+i) + pi + L  ==  b(i+o) + pi  (mod bN)
        rho = (b * (o - r) - L) % bN
        t = k * lay.spacing + rho
        k += 1
        offsets.append(t)
        blocks_sum += block_mult(t, c, K, pi, b, r)
        for i in range(N):
            A |= 1 << (t + b * (r + i) + pi + L)
    # extra block: single term 2^t 2^(br); always-one bit of cell i at t + b(r+i)
    rho0 = (b * (o - r)) % bN
    t = k * lay.spacing + rho0
    offsets.append(t)
    blocks_sum += (1 << (b * r)) << t
    for i in range(N):
        A |= 1 << (t + b * (r + i))
    M = blocks_sum * lay.rep
    D = (1 << bN) - 1
    # sanity on offsets: consecutive differ by more than beta
    srt = sorted(offsets)
    assert all(srt[i + 1] - srt[i] > lay.beta for i in range(len(srt) - 1))
    return b, pi, M, A, D, dict(L=L, P=lay.P, beta=lay.beta, spacing=lay.spacing, nblocks=len(offsets))


def slot_check(x, lay, c, K, r):
    """Check field identity and slot bounds for one block with t = 0 on row x.
    Returns max slot value; asserts slots < 2^(2pi+ell+2) and bit pi+ell of slot r+i is h."""
    b, pi, ell, N = lay.b, lay.pi, lay.ell, lay.N
    Xp = encode(x, b, pi) * lay.rep
    prod_ = Xp * block_mult(0, c, K, pi, b, r)
    # compute slot contents directly from the definition, not from the product
    v = [1 + (xi << pi) for xi in x]
    PN = lay.P * N
    slots = {}
    for cc in range(PN):
        for d in range(r):
            s = cc + r - d
            slots[s] = slots.get(s, 0) + c[d] * v[cc % N]
        s = cc + r
        slots[s] = slots.get(s, 0) + (K << pi) * v[cc % N]
    bound = 1 << (2 * pi + ell + 2)
    mx = max(slots.values())
    assert mx < bound, (mx, bound)
    recon = sum(val << (b * s) for s, val in slots.items())
    assert recon == prod_
    assert prod_ < (1 << lay.beta)
    for i in range(N):
        Fi = slots[r + i]
        h = ((K + sum(c[d] * x[(i + d) % N] for d in range(r))) >> ell) & 1
        assert (Fi >> (pi + ell)) & 1 == h
    return mx


def run_thm(Nmax):
    t0 = time.time()
    total = 0
    maxinfo = {}
    for k in (1, 2, 3):
        r, o = 2 * k + 1, k
        for rule in range(256):
            g = eca_table(rule, k)
            for N in range(1, Nmax + 1):
                b, pi, M, A, D, info = build_thm95(g, r, o, N)
                maxinfo[(k, N)] = (b, pi, info['L'], info['P'], info['nblocks'], M.bit_length())
                for x in all_rows(N):
                    y = eca_steps(rule, x, k)
                    lhs = encode(y, b, pi)
                    rhs = ((encode(x, b, pi) * M) & A) % D
                    if lhs != rhs:
                        print("FAIL", k, rule, N, x)
                        return
                    assert lhs < D
                    total += 1
        print(f"k={k}: all 256 rules OK up to N={Nmax}; elapsed {time.time()-t0:.1f}s")
    print("rows checked:", total, "(expected", 3 * 256 * sum(2 ** N for N in range(1, Nmax + 1)), ")")
    for k in (1, 2, 3):
        for N in (1, 2, Nmax):
            b, pi, L, P, nb, Mbits = maxinfo[(k, N)]
            print(f"  k={k} N={N}: L={L} pi={pi} b={b} P={P} (blocks for rule {255}: {nb}) M bits={Mbits}")


def run_prop(Nmax):
    t0 = time.time()
    reps = blf_representations(3, 3)
    r, o = 3, 1
    rules = [R for R in range(256) if R in reps]
    print("BLF elementary rules:", len(rules))
    rng = random.Random(1)
    # all representations with j <= 2, to test more than one (ell, K, c) per rule
    allreps = {}
    from itertools import product as P_
    for j in range(3):
        mod = 1 << (j + 1)
        for K in range(mod):
            for a in P_(range(mod), repeat=3):
                t = 0
                for l, c_, rr in P_((0, 1), repeat=3):
                    val = K + a[0] * l + a[1] * c_ + a[2] * rr
                    t |= ((val >> j) & 1) << (4 * l + 2 * c_ + rr)
                allreps.setdefault(t, []).append((j, K, a))
    total = 0
    maxslot_ratio = 0.0
    for R in rules:
        cand = [reps[R]] + rng.sample(allreps[R], min(3, len(allreps[R])))
        for (ell, K, c) in cand:
            for N in range(1, Nmax + 1):
                lay = Layout(r, N, ell)
                b, pi = lay.b, lay.pi
                M = block_mult(0, list(c), K, pi, b, r) * lay.rep
                A = sum(1 << (b * (r + i) + pi + ell) for i in range(N))
                pos = [b * (r + ((j - o) % N)) + pi + ell for j in range(N)]
                assert len(set(pos)) == N
                for x in all_rows(N):
                    y = eca_steps(R, x, 1)
                    lhs = (encode(x, b, pi) * M) & A
                    rhs = sum(y[j] << pos[j] for j in range(N))
                    if lhs != rhs:
                        print("FAIL prop", R, (ell, K, c), N, x)
                        return
                    total += 1
                    if N <= 5:
                        mx = slot_check(x, lay, list(c), K, r)
                        maxslot_ratio = max(maxslot_ratio, mx / (1 << (2 * pi + ell + 2)))
    print(f"Prop 9.4 forward: OK on {total} (rule, representation, row) cases, N <= {Nmax}; "
          f"max slot / 2^(2pi+ell+2) = {maxslot_ratio:.4f}; {time.time()-t0:.1f}s")


def run_big(trials):
    t0 = time.time()
    rng = random.Random(110)
    for k in (2, 3):
        r, o, N = 2 * k + 1, k, 256
        g = eca_table(110, k)
        b, pi, M, A, D, info = build_thm95(g, r, o, N)
        print(f"Rule 110, k={k}, N=256: L={info['L']} pi={pi} b={b} P={info['P']} blocks={info['nblocks']} "
              f"bits: M={M.bit_length()} A={A.bit_length()} D={D.bit_length()}")
        for tr in range(trials):
            if tr == 0:
                x = tuple([0] * N)
            elif tr == 1:
                x = tuple([0] * (N - 1) + [1])
            else:
                x = tuple(rng.randint(0, 1) for _ in range(N))
            y = eca_steps(110, x, k)
            ok = encode(y, b, pi) == ((encode(x, b, pi) * M) & A) % D
            if not ok:
                print("FAIL big", k, tr)
                return
        print(f"  {trials} rows OK ({time.time()-t0:.1f}s)")


if __name__ == "__main__":
    mode = sys.argv[1]
    arg = int(sys.argv[2]) if len(sys.argv) > 2 else None
    if mode == "thm":
        run_thm(arg or 8)
    elif mode == "prop":
        run_prop(arg or 8)
    elif mode == "big":
        run_big(arg or 10)

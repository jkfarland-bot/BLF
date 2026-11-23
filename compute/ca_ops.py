"""Exact check of the operation-count constructions of Section 9 of the BLF paper.

Encoding of a cyclic row x_0..x_{N-1}: E(x) = sum_i (1 + 2^pi x_i) 2^(b i).
Table g on windows of w cells; output cell j uses the window starting at cell j - o (indices mod N).

Theorem 9.5 (three operations): E(y) = ((E(x) * M) AND A) mod (2^(bN) - 1) for every row x.
Proposition 9.4 (multiply then AND): for a BLF table, (E(x) * M) AND A = sum_j y_j 2^(e_j) for every row.

Checks: every elementary rule at k = 1, 2, 3 steps (w = 3, 5, 7, o = k) on every row with N <= NMAX,
the BLF readout for every BLF elementary rule (k = 1) on every row with N <= NMAX,
and random rows of 256 cells for Rule 110.
Usage: python3 ca_ops.py [NMAX]
"""
import itertools
import random
import sys


def params(w):
    L = w.bit_length()            # 2^L > w
    pi = L + 1 + (w + 1).bit_length() + 1   # 2^pi > sum of coefficients < w 2^(L+1); pi > L
    f = 2 * pi + L + 3            # field width
    return L, pi, f


def blf_rep(table, w, maxbit=6):
    """Find (j, K, c) with table[x] = bit j of K + c.x, c_d, K in [0, 2^(j+1)); x as bit tuple, x[0] first cell."""
    pts = list(itertools.product((0, 1), repeat=w))
    for j in range(maxbit + 1):
        m = 1 << (j + 1)
        for c in itertools.product(range(m), repeat=w):
            vals = [sum(ci * xi for ci, xi in zip(c, x)) for x in pts]
            for K in range(m):
                if all(((K + v) >> j) & 1 == table[x] for v, x in zip(vals, pts)):
                    return j, K, c
    return None


def field_terms(K, c, j, w, pi):
    """Multiplier terms (coefficient, cell offset d) of one field reading g = bit j of K + c.x at bit pi + j."""
    terms = [(c[d], d) for d in range(w)]
    terms.append(((K << pi), 0))   # gamma v_i = 2^pi K (1 + 2^pi x_i)
    return terms


class Machine:
    def __init__(self, N, w, o, fields, b, pi):
        """fields: list of (terms, read_bit, target_offset_in_slot) blocks."""
        self.N, self.w, self.o, self.b, self.pi = N, w, o, b, pi
        R = (w - 1 + N - 1) // N + 1          # replicas so that cells i + d < R N
        W = w
        span = b * N * ((W + (R + 2) * N + 2) // N + 1)   # a multiple of bN, wider than a block
        M = 0
        A = 0
        for k, (terms, read, target) in enumerate(fields):
            # want t + b(W + i) + read == b(i + o) + target (mod bN)
            r = (b * (o - W) + target - read) % (b * N)
            t = k * span + r
            for coef, d in terms:
                M += coef << (t + b * (W - d))
            for i in range(N):
                A |= 1 << (t + b * (W + i) + read)
        rep = sum(1 << (b * N * r_) for r_ in range(R))
        self.M = M * rep
        self.A = A
        self.D = (1 << (b * N)) - 1

    def step3(self, X):
        return ((X * self.M) & self.A) % self.D


def encode(x, b, pi):
    return sum((1 + (xi << pi)) << (b * i) for i, xi in enumerate(x))


def three_op_machine(table, w, o, N):
    L, pi, f = params(w)
    b = f
    fields = []
    # constant block: field content v_i = 1 + 2^pi x_i, read bit 0, target offset 0
    fields.append(([(1, 0)], 0, 0))
    for m in itertools.product((0, 1), repeat=w):
        if table[m]:
            # [window = m] = bit L of (2^L - |m|) + sum (2 m_d - 1) x_d; coefficients mod 2^(L+1)
            mod = 1 << (L + 1)
            c = tuple(1 if md else mod - 1 for md in m)
            K = (1 << L) - sum(m)
            fields.append((field_terms(K, c, L, w, pi), pi + L, pi))
    return Machine(N, w, o, fields, b, pi), b, pi


def eca_table(rule, k):
    w = 2 * k + 1
    tab = {}
    for x in itertools.product((0, 1), repeat=w):
        row = list(x)
        for _ in range(k):
            row = [(rule >> (4 * a + 2 * bb + c)) & 1 for a, bb, c in zip(row, row[1:], row[2:])]
        tab[x] = row[0]
    return tab


def step_row(x, table, w, o):
    N = len(x)
    return [table[tuple(x[(j - o + d) % N] for d in range(w))] for j in range(N)]


def check_three(NMAX):
    count = 0
    for k in (1, 2, 3):
        w = 2 * k + 1
        for rule in range(256):
            tab = eca_table(rule, k)
            for N in range(1, NMAX + 1):
                mach, b, pi = three_op_machine(tab, w, k, N)
                for xs in itertools.product((0, 1), repeat=N):
                    y = step_row(list(xs), tab, w, k)
                    assert mach.step3(encode(xs, b, pi)) == encode(y, b, pi), (rule, k, N, xs)
                    count += 1
        print(f"three operations: k = {k}, all 256 rules, every row with N <= {NMAX}: ok")
    return count


def check_two_blf(NMAX):
    count = 0
    for k in (1,):
        w = 2 * k + 1
        L, pi, f = params(w)
        nblf = 0
        tables = {}
        for rule in range(256):
            tables.setdefault(tuple(sorted(eca_table(rule, k).items())), eca_table(rule, k))
        for key, tab in tables.items():
            rep = blf_rep(tab, w, maxbit=3)
            if rep is None:
                continue
            nblf += 1
            j, K, c = rep
            pi2 = max(pi, j + 1 + (sum(c) + 1).bit_length() + 1)
            b = 2 * pi2 + j + 3 + (K.bit_length())
            for N in range(1, NMAX + 1):
                mach = Machine(N, w, k, [(field_terms(K, c, j, w, pi2), pi2 + j, 0)], b, pi2)
                # read positions: t + b(W + i) + read for the single block
                R = (w - 1 + N - 1) // N + 1
                r = (b * (k - w) + 0 - (pi2 + j)) % (b * N)
                pos = [r + b * (w + i) + pi2 + j for i in range(N)]
                Mraw = mach.M
                for xs in itertools.product((0, 1), repeat=N):
                    y = step_row(list(xs), tab, w, k)
                    Z = (encode(xs, b, pi2) * Mraw) & mach.A
                    assert Z == sum(yi << p for yi, p in zip([y[(i + k) % N] for i in range(N)], pos)), (k, N, xs)
                    count += 1
        print(f"multiply then AND: k = {k}, {nblf} distinct BLF tables among the elementary rules, every row with N <= {NMAX}: ok")
    return count


def check_long():
    rnd = random.Random(110)
    for k in (1, 2, 3):
        w = 2 * k + 1
        tab = eca_table(110, k)
        N = 256
        mach, b, pi = three_op_machine(tab, w, k, N)
        for _ in range(20):
            xs = [rnd.randrange(2) for _ in range(N)]
            assert mach.step3(encode(xs, b, pi)) == encode(step_row(xs, tab, w, k), b, pi)
        print(f"three operations: Rule 110, k = {k}, 20 random rows of 256 cells: ok")


if __name__ == "__main__":
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    n1 = check_three(NMAX)
    n2 = check_two_blf(NMAX)
    check_long()
    print(f"rows checked: {n1} (three operations), {n2} (multiply then AND)")

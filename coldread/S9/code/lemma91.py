"""Lemma 9.1: run the construction of the proof on random and adversarial A, D and check every
step and the conclusion.

For each instance (r, N, a_*, a_i, D):
  s_i = frac(a_i / D); bins of length 1/(2r); windows V_k = {kr, ..., kr+r-1}, k < m = floor(N/r);
  find a pair good for every bin (assert one exists); assign partners (same bin, outside V u V',
  distinct); compute mu, M (V part) and mu', M' (V' part); decide the case as the proof says; build
  the 2^r rows; check floor(A/D) is integer affine in the free window, that every cell outside it is
  constant or the complement of a cell of the window, and that the free window takes all values.
Also: the literal reading of "exchange the roles of V and V'" (fix x_V' at a MAXIMIZER of the
V' part in the second case) is tested and its failures counted.
Also: the counting step is tight: for m = 2r+2 there are bin assignments with no good pair.
"""
import random
import sys
import time
from fractions import Fraction
from itertools import product, combinations
from math import floor, ceil


def is_int_affine(vals, r):
    """vals: dict z-tuple -> int. True iff vals(z) = vals(0) + sum_d (vals(e_d) - vals(0)) z_d."""
    z0 = tuple([0] * r)
    base = vals[z0]
    co = []
    for d in range(r):
        e = [0] * r
        e[d] = 1
        co.append(vals[tuple(e)] - base)
    return all(vals[z] == base + sum(c * zd for c, zd in zip(co, z)) for z in vals)


def find_good_pairs(bins_of, r, m):
    nb = 2 * r
    tot = [0] * nb
    for bn in bins_of:
        tot[bn] += 1
    good = []
    for k, l in combinations(range(m), 2):
        cnt = [0] * nb
        for c in list(range(k * r, k * r + r)) + list(range(l * r, l * r + r)):
            cnt[bins_of[c]] += 1
        if all(2 * cnt[q] <= tot[q] for q in range(nb)):
            good.append((k, l))
    return good


def run_instance(r, a_star, a, D, rng, stats):
    N = len(a)
    m = N // r
    s = [Fraction(ai, D) - (ai // D) for ai in a]
    bins_of = [floor(si * 2 * r) for si in s]
    assert all(0 <= q < 2 * r for q in bins_of)
    good = find_good_pairs(bins_of, r, m)
    assert good, "no good pair: counting argument contradicted"
    k, l = rng.choice(good)
    V = list(range(k * r, k * r + r))
    Vp = list(range(l * r, l * r + r))
    inside = set(V) | set(Vp)
    pool = {}
    for c in range(N):
        if c not in inside:
            pool.setdefault(bins_of[c], []).append(c)
    partner = {}
    for c in V + Vp:
        lst = pool.get(bins_of[c], [])
        assert lst, "no partner available"
        partner[c] = lst.pop(rng.randrange(len(lst)))
        assert abs(s[c] - s[partner[c]]) < Fraction(1, 2 * r)
    assert len(set(partner.values())) == len(partner)
    used = set(partner.values())
    others = [c for c in range(N) if c not in inside and c not in used]
    fixed = {c: rng.randint(0, 1) for c in others}
    s_star = Fraction(a_star, D) - (a_star // D)
    Phi0 = s_star + sum(s[partner[c]] for c in V + Vp) + sum(s[c] * fixed[c] for c in others)
    dV = [s[c] - s[partner[c]] for c in V]
    dVp = [s[c] - s[partner[c]] for c in Vp]
    mu, Mx = sum(d for d in dV if d < 0), sum(d for d in dV if d > 0)
    mup, Mxp = sum(d for d in dVp if d < 0), sum(d for d in dVp if d > 0)
    assert Mx - mu < Fraction(1, 2) and Mxp - mup < Fraction(1, 2)
    I = (Phi0 + mu + mup, Phi0 + Mx + mup)
    Ip = (Phi0 + Mx + mup, Phi0 + Mx + Mxp)
    assert Ip[1] - I[0] < 1
    n = ceil(I[0])
    case1 = n <= I[1]
    maxV = [1 if d > 0 else 0 for d in dV]
    minVp = [1 if d < 0 else 0 for d in dVp]
    maxVp = [1 if d > 0 else 0 for d in dVp]

    def build_and_check(free, fixed_win, fixed_vals):
        vals = {}
        rows = []
        for z in product((0, 1), repeat=r):
            x = [None] * N
            for c, zc in zip(free, z):
                x[c] = zc
            for c, vc in zip(fixed_win, fixed_vals):
                x[c] = vc
            for c in V + Vp:
                x[partner[c]] = 1 - x[c]
            for c, vc in fixed.items():
                x[c] = vc
            assert None not in x
            Aval = a_star + sum(ai * xi for ai, xi in zip(a, x))
            vals[z] = Aval // D
            rows.append(x)
        return vals, rows

    if case1:
        free, fw, fv = Vp, V, maxV
    else:
        free, fw, fv = V, Vp, minVp
    vals, rows = build_and_check(free, fw, fv)
    ok = is_int_affine(vals, r)
    assert ok, "conclusion fails"
    # every cell outside the free window constant or complement of a cell of the window
    for c in range(N):
        if c in free:
            continue
        col = [x[c] for x in rows]
        if len(set(col)) == 1:
            continue
        assert any(all(x[c] == 1 - x[w] for x in rows) for w in free)
    stats['case1' if case1 else 'case2'] += 1
    # literal "exchange roles" reading in case 2: fix x_V' at a maximizer, vary x_V
    if not case1:
        vals2, _ = build_and_check(V, Vp, maxVp)
        if not is_int_affine(vals2, r):
            stats['literal_exchange_fails'] += 1


def gen_instance(r, N, rng, mode):
    D = rng.choice([7, 97, 1000, 65536, 999983, 10 ** 9 + 7])
    if mode == "uniform":
        a = [rng.randint(-5 * D, 5 * D) for _ in range(N)]
    elif mode == "clustered":
        # few bins, cells of a bin concentrated in few windows
        nb = rng.randint(1, 2 * r)
        bins = rng.sample(range(2 * r), nb)
        a = []
        for c in range(N):
            w = c // r
            q = bins[(w * 7 + rng.randint(0, 1)) % nb] if rng.random() < 0.7 else rng.choice(bins)
            lo, hi = q * D // (2 * r) + 1, (q + 1) * D // (2 * r) - 1
            if lo > hi:
                lo = hi = q * D // (2 * r)
            frac_num = rng.randint(lo, max(lo, hi))
            a.append(rng.randint(-3, 3) * D + frac_num)
    else:  # near-boundary: fractional parts near bin edges
        a = []
        for c in range(N):
            q = rng.randrange(2 * r)
            edge = (q * D) // (2 * r)
            a.append(rng.randint(-3, 3) * D + min(D - 1, max(0, edge + rng.choice([-1, 0, 1, 2]))))
    a_star = rng.randint(-10 * D, 10 * D)
    return a_star, a, D


def tight_example(r):
    """m = 2r+2 windows: 2r-1 stars centred at V_0..V_{2r-2} and one triangle on the last three.
    Returns True if no pair is good."""
    m = 2 * r + 2
    N = m * r
    bins_of = [None] * N
    # star bins q = 0..2r-2: one cell of bin q in window V_q; triangle bin q = 2r-1: equal cells in
    # V_{m-3}, V_{m-2}, V_{m-1}. Remaining cells: spread so as not to spoil (put in their own star bin's centre).
    for q in range(2 * r - 1):
        for c in range(q * r, q * r + r):
            bins_of[c] = q
    for w in (m - 3, m - 2, m - 1):
        for c in range(w * r, w * r + r):
            bins_of[c] = 2 * r - 1
    good = find_good_pairs(bins_of, r, m)
    return len(good) == 0


def main(trials=300, seed=91):
    rng = random.Random(seed)
    t0 = time.time()
    stats = {'case1': 0, 'case2': 0, 'literal_exchange_fails': 0}
    n_inst = 0
    for r in (1, 2, 3, 4, 5):
        Nmin = r * (2 * r + 3)
        for N in (Nmin, Nmin + r - 1, Nmin + 2 * r + 1):
            for mode in ("uniform", "clustered", "edge"):
                for _ in range(trials if r <= 3 else max(10, trials // 10)):
                    a_star, a, D = gen_instance(r, N, rng, mode)
                    run_instance(r, a_star, a, D, rng, stats)
                    n_inst += 1
    print(f"Lemma 9.1 construction: {n_inst} instances OK (r = 1..5, N from r(2r+3)); "
          f"case counts {stats}; {time.time()-t0:.1f}s")
    for r in (1, 2, 3, 4, 5):
        print(f"  counting step tight at m = 2r+2 (r={r}): no good pair in star/triangle example: {tight_example(r)}")


if __name__ == "__main__":
    main(*(int(x) for x in sys.argv[1:]))

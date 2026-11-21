"""Independent exact-arithmetic tests of Lemma 3 of PROOF_R116 and its intermediate claims.

Usage: python3 lemma3_check.py seed
"""
import sys, random, itertools
from fractions import Fraction as Fr
from math import floor

random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)

def verts(n):
    return list(itertools.product([0, 1], repeat=n))

def val(u, x):
    t, r = u
    return t + sum(ri * xi for ri, xi in zip(r, x))

def generic(u, n):
    return all(val(u, x).denominator != 1 for x in verts(n))

def Fvec(u, n):
    return {x: floor(val(u, x)) for x in verts(n)}

def e(n, i):
    return tuple(1 if k == i else 0 for k in range(n))

def chamber_key(F, n):
    z = (0,) * n
    d = [F[e(n, i)] - F[z] for i in range(n)]
    return tuple(F[x] - F[z] - sum(di * xi for di, xi in zip(d, x)) for x in verts(n))

def class_key(F, n):
    z = (0,) * n
    f = {x: F[x] & 1 for x in F}
    b = [f[e(n, i)] ^ f[z] for i in range(n)]
    return tuple(f[x] ^ f[z] ^ (sum(bi * xi for bi, xi in zip(b, x)) & 1) for x in verts(n))

def neg(u):
    return (-u[0], tuple(-ri for ri in u[1]))

def flip(x, j):
    return tuple(1 - xi if k == j else xi for k, xi in enumerate(x))

class Fail(Exception):
    pass

def need(cond, msg):
    if not cond:
        raise Fail(msg)

stats = {}

def bump(k):
    stats[k] = stats.get(k, 0) + 1

def check_pair(u, w, n):
    """u, w generic with f_u XOR f_w affine. Verifies every claim of Lemma 3."""
    V = verts(n); z = (0,) * n
    Fu, Fw = Fvec(u, n), Fvec(w, n)
    dif = {x: (Fu[x] ^ Fw[x]) & 1 for x in V}
    need(class_key(Fu, n) == class_key(Fw, n), "not same class")
    # lift the affine difference to m in Lambda (0/1 coefficients)
    b0 = dif[z]; b = [dif[e(n, i)] ^ b0 for i in range(n)]
    w2 = (w[0] + b0, tuple(wi + bi for wi, bi in zip(w[1], b)))
    F, G = Fu, Fvec(w2, n)
    need(chamber_key(G, n) == chamber_key(Fw, n), "lift changed chamber")
    need(all((F[x] - G[x]) % 2 == 0 for x in V), "F != G mod 2 after lift")
    a = {x: val(u, x) - F[x] for x in V}; c = {x: val(w2, x) - G[x] for x in V}
    need(all(0 < a[x] < 1 and 0 < c[x] < 1 for x in V), "a,c not in (0,1)")
    k = [floor(ri) for ri in u[1]]; al = [ri - ki for ri, ki in zip(u[1], k)]
    mm = [floor(ri) for ri in w2[1]]; be = [ri - mi for ri, mi in zip(w2[1], mm)]
    A = {}; C = {}
    for i in range(n):
        for x in V:
            if x[i] == 0:
                y = flip(x, i)
                A[i, x] = 1 if a[x] + al[i] >= 1 else 0
                C[i, x] = 1 if c[x] + be[i] >= 1 else 0
                need(F[y] - F[x] == k[i] + A[i, x], "F step formula")
                need(G[y] - G[x] == mm[i] + C[i, x], "G step formula")
                need(a[y] == a[x] + al[i] - A[i, x], "a step formula")
                need(c[y] == c[x] + be[i] - C[i, x], "c step formula")
    # types
    typ = []
    for i in range(n):
        edges = [x for x in V if x[i] == 0]
        isS = all(A[i, x] == C[i, x] for x in edges)
        isD = all(A[i, x] == 1 - C[i, x] for x in edges)
        need(isS != isD, "direction has no type or two types")
        need(isS == ((mm[i] - k[i]) % 2 == 0), "type parity mismatch")
        typ.append('S' if isS else 'D')
    IS = [i for i in range(n) if typ[i] == 'S']; ID = [i for i in range(n) if typ[i] == 'D']
    rigid = [len({A[i, x] for x in V if x[i] == 0}) == 1 for i in range(n)]
    # Step 1
    for i in IS:
        for j in ID:
            for x in V:
                if x[i] == 0:
                    need(A[i, x] == A[i, flip(x, j)], "Step 1: A_i not D-invariant")
                if x[j] == 0:
                    need(A[j, x] == A[j, flip(x, i)], "Step 1: A_j not S-invariant")
    # Step 2
    g = {x: a[x] + c[x] - 1 for x in V}; h = {x: a[x] - c[x] for x in V}
    def proj(x, keep):
        return tuple(xi if kk in keep else 0 for kk, xi in enumerate(x))
    for x in V:
        xS = proj(x, IS); xD = proj(x, ID)
        LD = sum((al[j] + be[j] - 1) * x[j] for j in ID)
        LS = sum((al[i] - be[i]) * x[i] for i in IS)
        need(g[x] == g[xS] + LD, "Step 2: g decomposition")
        need(h[x] == h[xD] + LS, "Step 2: h decomposition")
        need(abs(g[x]) + abs(h[x]) < 1, "(*) fails")
    # Step 3 conclusion
    allS = all(rigid[i] for i in IS); allD = all(rigid[j] for j in ID)
    need(allS or allD, "Step 3: non-rigid S and D directions coexist")
    # Step 4
    ch_u = chamber_key(Fu, n); ch_nu = chamber_key(Fvec(neg(u), n), n); ch_w = chamber_key(Fw, n)
    need(ch_w in (ch_u, ch_nu), "LEMMA 3 FAILS: w not in chamber of u or -u")
    if allD:
        Dd = {x: (F[x] - G[x]) // 2 for x in V}
        need(chamber_key(Dd, n) == (0,) * len(V), "Step 4: D not affine")
        need(ch_w == ch_u, "Step 4: expected same chamber")
    if allS:
        Ss = {x: (F[x] + G[x]) // 2 for x in V}
        need(chamber_key(Ss, n) == (0,) * len(V), "Step 4: S not affine")
        need(ch_w == ch_nu, "Step 4: expected antipodal chamber")
    bump(('pairs', n))
    if IS and ID:
        bump(('both_types', n))
    if any(not rigid[i] for i in IS) and IS and ID:
        bump(('nonrigidS_with_D', n))
    if any(not rigid[j] for j in ID) and IS and ID:
        bump(('nonrigidD_with_S', n))
    bump(('same' if ch_w == ch_u else 'anti', n))
    if ch_u == ch_nu:
        bump(('selfanti', n))

def rand_generic(n, q):
    while True:
        u = (Fr(random.randrange(-3 * q, 3 * q), q),
             tuple(Fr(random.randrange(-3 * q, 3 * q), q) for _ in range(n)))
        if generic(u, n):
            return u

def rand_generic_wild(n):
    while True:
        q = random.choice([7, 11, 13, 17, 19, 23, 29, 31, 97, 101, 1009])
        u = rand_generic(n, q)
        return u

def dist_to_class(Fu, Fw, n):
    # Hamming distance of f_u XOR f_w to the nearest GF(2)-affine function
    V = verts(n)
    d = [(Fu[x] ^ Fw[x]) & 1 for x in V]
    best = len(V)
    for coeffs in itertools.product([0, 1], repeat=n + 1):
        aff = [(coeffs[0] + sum(ci * xi for ci, xi in zip(coeffs[1:], x))) & 1 for x in V]
        best = min(best, sum(di ^ ai for di, ai in zip(d, aff)))
    return best

# Experiment A: random pairs, check implication only when hypothesis holds
def expA(n, trials):
    hits = 0
    for _ in range(trials):
        u = rand_generic_wild(n); w = rand_generic_wild(n)
        if class_key(Fvec(u, n), n) == class_key(Fvec(w, n), n):
            hits += 1
            check_pair(u, w, n)
    return hits

# Experiment B: collisions among many small-denominator samples, grouped by class
def expB(n, samples, q):
    byclass = {}
    pairs = 0
    for _ in range(samples):
        u = rand_generic(n, q)
        Fu = Fvec(u, n)
        ck = class_key(Fu, n); hk = chamber_key(Fu, n)
        lst = byclass.setdefault(ck, {})
        if hk not in lst:
            for hk2, u2 in lst.items():
                check_pair(u, u2, n); check_pair(u2, u, n); pairs += 2
            lst[hk] = u
        elif random.random() < 0.05:
            check_pair(u, lst[hk], n); pairs += 1
    multi = sum(1 for v in byclass.values() if len(v) == 2)
    over = sum(1 for v in byclass.values() if len(v) > 2)
    return pairs, len(byclass), sum(len(v) for v in byclass.values()), multi, over

# Experiment C: adversarial hill climb. Start w away from chambers of u and -u, move w
# by random rational steps to reduce the distance to the class of u; check when it hits 0.
def expC(n, starts, steps):
    hits = 0
    for _ in range(starts):
        u = rand_generic_wild(n); Fu = Fvec(u, n)
        cu = chamber_key(Fu, n); cnu = chamber_key(Fvec(neg(u), n), n)
        w = rand_generic_wild(n)
        if chamber_key(Fvec(w, n), n) in (cu, cnu):
            continue
        dcur = dist_to_class(Fu, Fvec(w, n), n)
        for _s in range(steps):
            scale = random.choice([1, 2, 4, 8, 16])
            den = random.choice([16, 31, 64, 97, 128])
            w2 = (w[0] + Fr(random.randint(-den, den), den * scale),
                  tuple(wi + (Fr(random.randint(-den, den), den * scale) if random.random() < 0.5 else 0)
                        for wi in w[1]))
            if not generic(w2, n):
                continue
            d2 = dist_to_class(Fu, Fvec(w2, n), n)
            if d2 <= dcur:
                w, dcur = w2, d2
            if dcur == 0:
                check_pair(u, w, n); hits += 1
                break
    return hits

if __name__ == '__main__':
    out = []
    for n in range(2, 7):
        hA = expA(n, {2: 4000, 3: 4000, 4: 3000, 5: 2000, 6: 1000}[n])
        out.append(f"A n={n}: random pairs with affine XOR checked = {hA}")
    for n, samples, q in [(2, 3000, 8), (3, 6000, 12), (4, 20000, 16), (5, 30000, 6), (5, 30000, 10), (6, 20000, 4), (6, 20000, 6)]:
        r = expB(n, samples, q)
        out.append(f"B n={n} q={q} samples={samples}: pairs checked={r[0]} classes seen={r[1]} "
                   f"chambers seen={r[2]} classes with 2 chambers={r[3]} classes with >2 chambers={r[4]}")
    for n in range(2, 7):
        hC = expC(n, {2: 300, 3: 300, 4: 200, 5: 150, 6: 80}[n], {2: 200, 3: 300, 4: 500, 5: 800, 6: 1200}[n])
        out.append(f"C n={n}: adversarial climbs reaching the class of u from outside chambers of +-u = {hC}")
    print("\n".join(out))
    print("stats:", dict(sorted(stats.items(), key=str)))
    print("ALL CHECKS PASSED")

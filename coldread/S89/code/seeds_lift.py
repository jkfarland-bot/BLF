"""Independent check of Lemmas 8.6 (seeds) and 8.7 (Walsh lift), written from the text.
Exact integer / Fraction arithmetic only."""
import sys
from fractions import Fraction
from math import comb

def chi(a, p):
    a %= p
    if a == 0: return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1

def seed(p):
    eps = chi(-1, p)
    idx = ['inf'] + list(range(p))          # fixed order a_0..a_p
    def K(a, b):
        if a == 'inf' and b == 'inf': return 0
        if a == 'inf': return 1
        if b == 'inf': return eps
        return chi(a - b, p)
    U = [[1, 1], [1, -1]]
    V = [[1, -1], [-eps, -eps]]
    n = p + 1; d = 2 * n
    # natural index (pair k, u) -> 2k+u ; u=0 top, u=1 bottom
    Hn = [[K(idx[ka], idx[kb]) * U[u][v] + (V[u][v] if ka == kb else 0)
           for kb in range(n) for v in range(2)] for ka in range(n) for u in range(2)]
    # checks on K
    Km = [[K(a, b) for b in idx] for a in idx]
    assert all(Km[j][i] == eps * Km[i][j] for i in range(n) for j in range(n))
    assert all(sum(Km[i][k] * Km[j][k] for k in range(n)) == (p if i == j else 0) for i in range(n) for j in range(n))
    # row order: bottom rows of pairs a_0..a_p, then top rows
    order = [2 * k + 1 for k in range(n)] + [2 * k for k in range(n)]
    H = [Hn[i][:] for i in order]
    D = [H[i][:] for i in range(n)]
    for k in range(n):
        if k < p:
            row = Hn[2 * (k + 1) + 1][:]          # bottom row of a_{k+1}
            row[2 * k] = -row[2 * k]; row[2 * k + 1] = -row[2 * k + 1]
        else:
            row = Hn[2 * 0 + 1][:]                # bottom row of a_0
            row[2 * p] = -row[2 * p]              # first entry in column pair a_p
        D.append(row)
    ip = lambda u, v: sum(a * b for a, b in zip(u, v))
    for i in range(d):
        if ip(D[i], H[i]) < 0: D[i] = [-e for e in D[i]]
    # normalisation
    f = H[0][:]
    H = [[h * f[j] for j, h in enumerate(row)] for row in H]
    D = [[x * f[j] for j, x in enumerate(row)] for row in D]
    for i in range(d):
        s = H[i][0]
        H[i] = [s * e for e in H[i]]; D[i] = [s * e for e in D[i]]
    # checks
    assert all(abs(e) == 1 for row in H + D for e in row)
    HHt = [[ip(H[i], H[j]) for j in range(d)] for i in range(d)]
    assert HHt == [[d if i == j else 0 for j in range(d)] for i in range(d)]
    assert all(e == 1 for e in H[0]) and all(H[i][0] == 1 for i in range(d))
    DHt = [[ip(D[i], H[j]) for j in range(d)] for i in range(d)]
    assert all(DHt[i][j] == 0 for i in range(d) for j in range(i + 1, d))
    diag = [DHt[i][i] for i in range(d)]
    assert diag == [d] * (d // 2) + [4] * (d // 2 - 1) + [2], diag
    return H, D, diag

def bareiss_det(M):
    M = [row[:] for row in M]; n = len(M); sign = 1; prev = 1
    for k in range(n - 1):
        if M[k][k] == 0:
            for i in range(k + 1, n):
                if M[i][k] != 0:
                    M[k], M[i] = M[i], M[k]; sign = -sign; break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return sign * M[n - 1][n - 1]

def solve(M, b):
    n = len(M)
    A = [[Fraction(x) for x in row] + [Fraction(b[i])] for i, row in enumerate(M)]
    for c in range(n):
        piv = next(i for i in range(c, n) if A[i][c] != 0)
        A[c], A[piv] = A[piv], A[c]
        pv = A[c][c]
        for i in range(n):
            if i != c and A[i][c] != 0:
                f = A[i][c] / pv
                A[i] = [x - f * y for x, y in zip(A[i], A[c])]
    return [A[i][n] / A[i][i] for i in range(n)]

def G(k, t):
    if t == 0: return [frozenset()]
    if t == k: return [frozenset(range(1, k + 1))]
    return G(k - 1, t) + [s | {k} for s in reversed(G(k - 1, t - 1))]

def subset_order(l):
    out = []
    for t in range(l + 1):
        lay = G(l, t)
        if t % 2 == 1: lay = lay[::-1]
        if t >= 1:
            assert lay[0 if t % 2 == 0 else -1] == frozenset(range(1, t + 1))
            assert lay[-1 if t % 2 == 0 else 0] == frozenset(list(range(1, t)) + [l])
        out += lay
    assert len(set(out)) == 2 ** l
    for R, S in zip(out, out[1:]):
        add = R < S and len(S - R) == 1
        exch = len(R) == len(S) and len(R ^ S) == 2
        assert add or exch, (R, S)
    return out

def lift(p, l):
    H, D, diag = seed(p)
    d = 2 * (p + 1); r = d * 2 ** l
    Ss = subset_order(l)
    xs = [tuple((v >> (l - 1 - k)) & 1 for k in range(l)) for v in range(2 ** l)]  # lex order
    xset = [frozenset(k + 1 for k in range(l) if x[k]) for x in xs]
    chiS = lambda S, X: -1 if len(S & X) % 2 else 1
    g = lambda b: H[d - 1] if b % 2 else [1] * d
    Q = [[chiS(Ss[b], X) * g(b)[j] * H[i][j] for X in xset for j in range(d)] for b in range(2 ** l) for i in range(d)]
    A = []
    for b in range(2 ** l):
        S = Ss[b]
        if b == 0:
            for i in range(d):
                A.append([D[i][j] for X in xset for j in range(d)])
            continue
        R = Ss[b - 1]; gb = g(b)
        Wgen = [frozenset([e]) for e in (R & S)] + [R ^ S]
        def inWperp(X):
            return all(len(w & X) % 2 == 0 for w in Wgen)
        A.append([chiS(R, X) * gb[j] * (2 * inWperp(X) - 1) for X in xset for j in range(d)])
        for i in range(1, d):
            A.append([(gb[j] * D[i][j]) if not (S & X) else (-chiS(S, X) * gb[j] * H[i - 1][j])
                      for X in xset for j in range(d)])
    assert all(abs(e) == 1 for row in A for e in row)
    # QQ^T = rI
    for a in range(0, r, max(1, r // 16)):
        for c in range(r):
            v = sum(x * y for x, y in zip(Q[a], Q[c]))
            assert v == (r if a == c else 0)
    assert all(Q[a][0] == 1 for a in range(r))
    # L = A Q^T / r
    L = [[Fraction(sum(x * y for x, y in zip(A[a], Q[c])), r) for c in range(r)] for a in range(r)]
    assert all(L[a][c] == 0 for a in range(r) for c in range(a + 1, r)), "L not lower triangular"
    lam = [Fraction(x, d) for x in diag]
    pred = []
    for b in range(2 ** l):
        t = len(Ss[b])
        if b == 0: pred += lam
        else: pred += [Fraction(1, 2 ** (t - 1))] + [lam[i] / 2 ** t for i in range(1, d)]
    assert [L[a][a] for a in range(r)] == pred, "diagonal mismatch"
    # beta bound and gamma
    s = d * (1 + l + comb(l, 2))
    assert len(Ss[s // d]) == 3 and len(Ss[s // d - 1]) == 2
    maxbeta = Fraction(0)
    for a in range(s + 1, r):
        t = len(Ss[a // d])
        for k in range(a):
            coef = 2 ** t * L[a][k] + (2 ** t if k == a - 1 else 0)   # beta_{ak}
            maxbeta = max(maxbeta, abs(coef))
    # forward substitution L u = e_s
    u = [Fraction(0)] * r
    for a in range(r):
        rhs = Fraction(1 if a == s else 0) - sum(L[a][k] * u[k] for k in range(a))
        u[a] = rhs / L[a][a]
    assert u[s] == 4 and all(u[k] == 0 for k in range(s))
    doubling = all(u[k + 1] >= 2 * u[k] >= 0 for k in range(s, r - 1))
    det = bareiss_det(A)
    x = solve(A, [1 if i == s else 0 for i in range(r)])
    P = Fraction(1)
    for t in range(3, l + 1):
        P *= (Fraction(d, 4) ** (d // 2) * Fraction(2 ** t - 4) ** d) ** comb(l, t)
    return dict(p=p, l=l, d=d, r=r, s=s, det=det, logdet=abs(det).bit_length() - 1,
                det_ok=abs(det) == 2 ** (r - 1), Ainv0s=x[0], sum_u_over_r=sum(u) / r,
                bound=P / r, ok=x[0] >= P / r, ur1=u[r - 1], P=P, maxbeta=maxbeta,
                doubling=doubling, A=A)

def pad(Ar, m):
    r = len(Ar); k = m - r; c = Ar[0][1]
    A = [row[:] + [row[1]] * k for row in Ar]
    for i in range(k):
        A.append(Ar[0][:] + [c * (1 if jj != i else -1) for jj in range(k)])
    return A

if __name__ == '__main__':
    for p in (3, 5, 7, 11, 13):
        H, D, diag = seed(p)
        print(f"seed p={p}: d={len(H)} HH^T=dI ok, diag(DH^T)={diag}, |det D|={abs(bareiss_det(D))} =2^{len(H)-1}? {abs(bareiss_det(D))==2**(len(H)-1)}")
    for (p, l) in [(3, 3), (5, 3), (7, 3)]:
        R = lift(p, l)
        print(f"lift p={p} l={l} r={R['r']} s={R['s']}: |det A|=2^{R['logdet']} (det_ok={R['det_ok']}), "
              f"(A^-1)_0s={R['Ainv0s']} (sum u/r = {R['sum_u_over_r']}), u_(r-1)={R['ur1']}, P={R['P']}, "
              f"P/r={R['bound']} ~ {float(R['bound']):.6g}, ok={R['ok']}, max|beta|={R['maxbeta']}, doubling={R['doubling']}")
        if (p, l) == (3, 3):
            for m in (66, 70):
                Am = pad(R['A'], m)
                dm = bareiss_det(Am)
                xm = solve(Am, [1 if i == R['s'] else 0 for i in range(m)])
                print(f"  padded m={m}: |det|=2^{abs(dm).bit_length()-1} ok={abs(dm)==2**(m-1)}, (A^-1)_0s={xm[0]}")
        sys.stdout.flush()

"""Check of Corollary 9.2 patterns and parity conditions, and the arithmetic of Prop 8.1 / Thm 8.4."""
import itertools, math
from fractions import Fraction

def R110(l, c, r): return (110 >> (4 * l + 2 * c + r)) & 1

def ksteps(w):
    while len(w) > 1:
        w = [R110(w[i], w[i + 1], w[i + 2]) for i in range(len(w) - 2)]
    return w[0]

def square_ok(g):  # g at 00,01,10,11 ; both monotone paths same total increase
    return (g[0] ^ g[1]) + (g[1] ^ g[3]) == (g[0] ^ g[2]) + (g[2] ^ g[3])

def allowed_parities(fv):
    out = []
    for b1, b2 in itertools.product((0, 1), repeat=2):
        g = [fv[2 * x + y] ^ (b1 * x) ^ (b2 * y) for x in (0, 1) for y in (0, 1)]
        if square_ok(g): out.append((b1, b2))
    return out

for k, prefs in [(2, ["000", "010"]), (3, ["00000", "00100"])]:
    r = 2 * k + 1
    for pre in prefs:
        fv = [ksteps([int(ch) for ch in pre] + [x, y]) for x in (0, 1) for y in (0, 1)]
        print(f"{k} steps, windows {pre}00..{pre}11: f = {fv}, allowed (b_(r-1) mod 2, b_r mod 2) = {allowed_parities(fv)}")
    # also: all squares of the last two inputs and their constraint types
    kinds = {}
    for pre in itertools.product((0, 1), repeat=r - 2):
        fv = tuple(ksteps(list(pre) + [x, y]) for x in (0, 1) for y in (0, 1))
        kinds.setdefault(tuple(allowed_parities(list(fv))), []).append(''.join(map(str, pre)))
    for kk, v in kinds.items():
        print(f"   constraint {kk}: {len(v)} prefixes, e.g. {v[:3]}")
    print(f"   N bound: floor(N/{r}) >= {2*r+3}  <=> N >= {r*(2*r+3)}")

# Prop 8.1 test vs j*(n)=n-1 for small n, and asymptotic
for n in range(1, 13):
    j = 0
    while not (2 ** (2 * j + 2 * n + 2) > (n + 1) ** 2 * (n + 2) ** (n + 2)): j += 1
    F = 0.5 * n * math.log2(n) - n
    print(f"n={n}: least j passing the test = {j}, n-1 = {n-1}, F(n) = {F:.2f}")

# exponent arithmetic
print("4^200 > 3^200*2^83:", 4 ** 200 > 3 ** 200 * 2 ** 83)
print("1-(8/15)*83/200 =", Fraction(1) - Fraction(8, 15) * Fraction(83, 200))
print("8/15 + (7/15)(21/40) =", Fraction(8, 15) + Fraction(7, 15) * Fraction(21, 40))
e3 = 1 - 8 / 15 * math.log2(4 / 3)
print("1-(8/15)log2(4/3) =", e3, " 292/375 =", 292 / 375, " 467/600 =", 467 / 600)
# covering inequality (kappa-3)(kappa-4)/2 >= 0 and identity
print("identity C(k,2)-3(k-2) == (k-3)(k-4)/2 for k<=100:",
      all(math.comb(k, 2) - 3 * (k - 2) == (k - 3) * (k - 4) // 2 for k in range(0, 101)))
# -log2(1-v) <= 2v on [0,1/2]
print("-log2(1-v)<=2v on grid:", all(-math.log2(1 - v / 1000) <= 2 * v / 1000 + 1e-15 for v in range(0, 501)))
# F(r) identity: prod over blocks of (d/4)^{d/2} 2^{d|S|} = 2^{F(r)}
for d, l in [(8, 3), (12, 5), (28, 7)]:
    r = d * 2 ** l
    lhs = sum((d / 2) * math.log2(d / 4) + d * t * math.comb(l, t) / 1 for t in [0]) # placeholder
    tot = sum(math.comb(l, t) * ((d / 2) * math.log2(d / 4) + d * t) for t in range(l + 1))
    print(f"d={d} l={l}: sum over blocks = {tot:.6f}, F(r) = {0.5*r*math.log2(r)-r:.6f}")

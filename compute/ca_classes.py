# Which of the 88 elementary CA equivalence classes are BLF (3 inputs l, c, r).
# BLF(3) computed here by brute force: bit j of K + a.x, 0 <= K, a_i < 2^(j+1), j <= 4
# (universal at j = 4 > needed bit 3, q = 16, by the minor bound 6: q > 4*6/2 = 12).
import itertools
pts = [(l, c, r) for l in (0, 1) for c in (0, 1) for r in (0, 1)]
def table(f):  # rule number: bit (4l+2c+r) is f(l,c,r)
    return sum(f[(l, c, r)] << (4*l + 2*c + r) for (l, c, r) in pts)
blf = set()
for j in range(5):
    M = 1 << (j + 1)
    for a in itertools.product(range(M), repeat=3):
        for K in range(M):
            blf.add(table({p: ((K + a[0]*p[0] + a[1]*p[1] + a[2]*p[2]) >> j) & 1 for p in pts}))
print("BLF(3) =", len(blf))
def refl(R): return sum(((R >> (4*l+2*c+r)) & 1) << (4*r+2*c+l) for (l, c, r) in pts)
def comp(R): return sum((1 - ((R >> (4*(1-l)+2*(1-c)+(1-r))) & 1)) << (4*l+2*c+r) for (l, c, r) in pts)
seen, classes = set(), []
for R in range(256):
    if R in seen: continue
    orb = {R, refl(R), comp(R), refl(comp(R))}
    seen |= orb; classes.append(min(orb))
print("classes:", len(classes))
inb = [c for c in classes if c in blf]
mixed = [c for c in classes if any(((x in blf) != (c in blf)) for x in {c, refl(c), comp(c), refl(comp(c))})]
out = [c for c in classes if c not in blf]
print("BLF classes:", len(inb), " non-BLF:", len(out), out, " mixed classes:", mixed)
print("rule 110 in BLF:", 110 in blf)

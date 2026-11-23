import itertools, sys
sys.path.insert(0, '/home/claude/vscratch3')
from indep import bits, is_blf_exact, affine_xors
def thresholds(n, R):
    S = set()
    pts = [bits(v, n) for v in range(1 << n)]
    for w in itertools.product(range(-R, R + 1), repeat=n):
        vals = [sum(a * b for a, b in zip(w, p)) for p in pts]
        cands = sorted(set(vals))
        for w0 in [-(c) for c in cands] + [-(cands[0]) + 1, -(cands[-1])]:
            # f = [0 < w0 + w.x]; also include thresholds strictly between values
            pass
        for t in range(min(vals) - 1, max(vals) + 2):
            S.add(sum(int(v > t) << i for i, v in enumerate(vals)))
    return S
def xor_set(S, n):
    A = [sum(b << i for i, b in enumerate(g)) for g in affine_xors(n)]
    return {s ^ a for s in S for a in A}
for n, R in ((1, 2), (2, 3), (3, 4), (4, 6)):
    T = thresholds(n, R)
    T2 = thresholds(n, R + 1)
    print("n=%d threshold functions: %d (with R+1: %d)" % (n, len(T), len(T2)))
for n in (3, 4):
    T = thresholds(n, 6 if n == 4 else 4)
    TXA = xor_set(T, n)
    N = 1 << n
    blf = {m for m in range(1 << N) if is_blf_exact(tuple((m >> v) & 1 for v in range(N)), n)} if n == 3 else None
    if n == 3:
        print("n=3 |TXA|=%d |BLF|=%d equal=%s" % (len(TXA), len(blf), TXA == blf))
    else:
        b1 = sum((((sum(bits(v, 4)) >> 1) & 1) << v) for v in range(16))
        ext = TXA | xor_set({b1}, 4)
        # BLF(4) by orbit test: affine-XOR orbits are unions, so test one rep per orbit
        blf = set(); seen = set(); A = [sum(b << i for i, b in enumerate(g)) for g in affine_xors(4)]
        for m in range(1 << 16):
            if m in seen: continue
            orb = {m ^ a for a in A}; seen |= orb
            if is_blf_exact(tuple((m >> v) & 1 for v in range(16)), 4): blf |= orb
        print("n=4 |TXA|=%d |TXA u (bit1 sum xor affine)|=%d |BLF|=%d equal=%s; bit1sum in TXA: %s, in BLF: %s"
              % (len(TXA), len(ext), len(blf), ext == blf, b1 in TXA, b1 in blf))

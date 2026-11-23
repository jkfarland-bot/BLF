"""The case excluded from Proposition 9.2 (a remainder after a floor or a remainder).

After Lemma 9.1 the intermediate value is an integer affine Lambda(z) of the r cells of one window.
(a) A floor next gives bit e of floor(Lambda/D) = floor(Lambda/(2^e D)) mod 2: BLF. Checked exhaustively
    for r = 3 and small coefficients.
(b) A remainder next gives bit e of (Lambda mod D), which need not be BLF: search r = 3 for examples.
    This shows that the proof's local argument cannot close the excluded case as it stands.
(c) Stress test of the counting step of Lemma 9.1 at m = 2r+3 with adversarial random bins.
"""
import random
from itertools import product, combinations
from blf_small import blf_representations


def tv(vals):
    t = 0
    for idx, v in enumerate(vals):
        t |= v << idx
    return t


def main():
    reps = blf_representations(3, 3)
    blf = set(reps)
    pts = list(product((0, 1), repeat=3))  # idx = 4 z0 + 2 z1 + z2 in this order
    floor_bad = 0
    mod_examples = []
    for K in range(-8, 9):
        for a in product(range(-8, 9), repeat=3):
            lam = [K + sum(ad * zd for ad, zd in zip(a, z)) for z in pts]
            for D in range(1, 13):
                for e in range(0, 4):
                    f_floor = tv([((l // D) >> e) & 1 for l in lam])
                    if f_floor not in blf:
                        floor_bad += 1
                    f_mod = tv([((l % D) >> e) & 1 for l in lam])
                    if f_mod not in blf and len(mod_examples) < 5:
                        mod_examples.append((K, a, D, e, f_mod))
    print("(a) bit e of floor(Lambda/D) non-BLF cases (expected 0):", floor_bad)
    print("(b) examples where bit e of (Lambda mod D) is not BLF (K, a, D, e, truth table):")
    for ex in mod_examples:
        print("   ", ex)
    # simplest one in words
    if mod_examples:
        K, a, D, e, t = min(mod_examples, key=lambda ex: (abs(ex[0]) + sum(map(abs, ex[1])) + ex[2]))
        print("    smallest found:", (K, a, D, e), "table over z = 000..111:", [(t >> i) & 1 for i in range(8)])

    # a clean example: Lambda = 1 + z0 + z1 + 2 z2, D = 5, e = 2
    lam = [1 + z[0] + z[1] + 2 * z[2] for z in pts]
    t = tv([((l % 5) >> 2) & 1 for l in lam])
    print("    clean example: Lambda = 1 + z0 + z1 + 2 z2, D = 5, bit 2 of Lambda mod 5:",
          [(t >> i) & 1 for i in range(8)], "= rule", t, "BLF:", t in blf,
          "| equals z2 AND (z0 XOR z1):", all(((t >> i) & 1) == (z[2] & (z[0] ^ z[1])) for i, z in enumerate(pts)))

    # (c) counting step stress test
    rng = random.Random(3)
    worst = 0
    for r in range(1, 7):
        m = 2 * r + 3
        for _ in range(3000):
            # adversarial: each bin places its cells mostly in one or two or three windows
            bins_of = []
            for w in range(m):
                for _c in range(r):
                    bins_of.append(None)
            for c in range(m * r):
                w = c // r
                q = (w * rng.choice([1, 1, 1, 2]) + rng.randint(0, 1)) % (2 * r)
                bins_of[c] = q if rng.random() < 0.8 else rng.randrange(2 * r)
            tot = [bins_of.count(q) for q in range(2 * r)]
            ngood = 0
            for k, l in combinations(range(m), 2):
                cnt = [0] * (2 * r)
                for c in list(range(k * r, k * r + r)) + list(range(l * r, l * r + r)):
                    cnt[bins_of[c]] += 1
                if all(2 * cnt[q] <= tot[q] for q in range(2 * r)):
                    ngood += 1
            assert ngood > 0, (r, bins_of)
    print("(c) counting step: a good pair existed in all 18000 adversarial assignments at m = 2r+3, r = 1..6")


if __name__ == "__main__":
    main()

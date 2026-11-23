"""BLF test for functions of few variables by exhaustive search over
bit j of K + a.x with 0 <= K, a_i < 2^(j+1) (enough by bit-j periodicity, Prop 2.1).

Used to find which elementary rules are BLF (expected: 208 of 256, Corollary 5.3)
and to give a representation (ell, K, c) for Proposition 9.4.
"""
from itertools import product


def truth_vector(f, n):
    """f: function on tuples -> bit; returns integer whose bit idx(z) is f(z),
    idx(z) = sum_d z_d 2^(n-1-d) (z_0 most significant, as in 4l+2c+r)."""
    t = 0
    for z in product((0, 1), repeat=n):
        idx = 0
        for zd in z:
            idx = 2 * idx + zd
        t |= f(z) << idx
    return t


def blf_representations(n, jmax):
    """Map truth vector -> first (j, K, a) found with j <= jmax (smallest j first)."""
    reps = {}
    pts = list(product((0, 1), repeat=n))
    for j in range(jmax + 1):
        mod = 1 << (j + 1)
        for K in range(mod):
            for a in product(range(mod), repeat=n):
                t = 0
                for z in pts:
                    idx = 0
                    for zd in z:
                        idx = 2 * idx + zd
                    val = K + sum(ad * zd for ad, zd in zip(a, z))
                    t |= ((val >> j) & 1) << idx
                if t not in reps:
                    reps[t] = (j, K, a)
    return reps


if __name__ == "__main__":
    for jmax in (2, 3):
        reps = blf_representations(3, jmax)
        print(f"n=3, j<={jmax}: {len(reps)} distinct BLF functions found")
    reps = blf_representations(3, 3)
    blf_rules = sorted(reps)  # truth vector of rule R is R itself with idx = 4l+2c+r
    nonblf = [R for R in range(256) if R not in reps]
    print("non-BLF elementary rules:", len(nonblf))
    # classes under reflection and complementation
    def reflect(R):
        return sum(((R >> (4 * l + 2 * c + r)) & 1) << (4 * r + 2 * c + l)
                   for l in (0, 1) for c in (0, 1) for r in (0, 1))
    def compl(R):
        return sum((1 - ((R >> (7 - i)) & 1)) << i for i in range(8))
    classes = {}
    for R in range(256):
        orb = {R, reflect(R), compl(R), reflect(compl(R))}
        classes[min(orb)] = orb
    nb = sorted(c for c, orb in classes.items() if not (orb & set(reps)))
    mixed = [c for c, orb in classes.items() if (orb & set(reps)) and (orb - set(reps))]
    print("classes:", len(classes), " non-BLF classes:", len(nb), nb, " mixed:", mixed)
    print("Rule 110 BLF:", 110 in reps, reps.get(110))

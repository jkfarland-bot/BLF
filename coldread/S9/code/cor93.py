"""Corollary 9.3 checks.
(a) the window values claimed in the proof for two and three steps of Rule 110;
(b) the square identity: for f = bit j of K + a.x and a square in directions p, q, with
    beta_l = floor(a_l / 2^j) mod 2, pattern 0,1,1,1 forces beta_p = beta_q and pattern
    0,1,0,0 forces beta_p != beta_q (exhaustive over small j, K, a_p, a_q and offsets);
(c) the N bounds: floor(N/r) >= 2r+3 iff N >= 65 (r=5), N >= 119 (r=7).
"""
from itertools import product
from common import eca_table


def window_values():
    out = []
    for k, prefixes in ((2, ("000", "010")), (3, ("00000", "00100"))):
        g = eca_table(110, k)
        for pre in prefixes:
            vals = [g[tuple(int(ch) for ch in pre + last)] for last in ("00", "01", "10", "11")]
            out.append((k, pre, vals))
    return out


def square_identity(jmax=4):
    """For every j <= jmax, every residue s_* (= rest of the form at the base corner), every
    a_p, a_q in [0, 2^(j+2)) (so floor(a/2^j) takes both parities), check the implications."""
    checked = 0
    for j in range(jmax + 1):
        mod = 1 << (j + 2)
        for S in range(1 << (j + 1)):          # value of K + (other terms) at the base corner, mod 2^(j+1)
            for ap in range(mod):
                for aq in range(mod):
                    f = [((S + ap * u + aq * w) >> j) & 1 for u, w in ((0, 0), (0, 1), (1, 0), (1, 1))]
                    bp, bq = (ap >> j) & 1, (aq >> j) & 1
                    if f == [0, 1, 1, 1]:
                        assert bp == bq, (j, S, ap, aq)
                    if f == [0, 1, 0, 0]:
                        assert bp != bq, (j, S, ap, aq)
                    checked += 1
    return checked


if __name__ == "__main__":
    for k, pre, vals in window_values():
        print(f"k={k}: windows {pre}00..{pre}11 -> values {vals}")
    print("square identity checked on", square_identity(), "cases: OK")
    for r, Nmin in ((5, 65), (7, 119)):
        Ns = [N for N in range(1, 400) if N // r >= 2 * r + 3]
        print(f"r={r}: least N with floor(N/r) >= 2r+3 is {Ns[0]} (claimed {Nmin}); 256 ok: {256 // r >= 2*r+3}")

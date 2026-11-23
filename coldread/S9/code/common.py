"""Common helpers for the independent check of Section 9 (written from the text only).

Conventions (from the Model paragraph):
  row x = (x_0, ..., x_{N-1}), indices mod N
  window of cell j: (x_{j-o}, ..., x_{j-o+r-1}), leftmost first
  E(x) = sum_i (1 + 2^pi x_i) 2^(b i)
  elementary rule R: f(l, c, r) = bit 4l + 2c + r of R
"""
from itertools import product


def bit(Y, e):
    """Bit e of an integer Y, as floor(Y / 2^e) mod 2 (two's complement for Y < 0)."""
    return (Y >> e) & 1


def eca_step(rule, x):
    """One step of elementary rule `rule` on the cyclic row x (tuple of 0/1)."""
    N = len(x)
    return tuple((rule >> (4 * x[(j - 1) % N] + 2 * x[j] + x[(j + 1) % N])) & 1 for j in range(N))


def eca_steps(rule, x, k):
    for _ in range(k):
        x = eca_step(rule, x)
    return x


def eca_table(rule, k):
    """The k-step table g on {0,1}^(2k+1), as a dict from tuples (leftmost first) to bits.
    Computed by composing on an open window (no wrap), as in the Model (r = 2k+1, o = k)."""
    r = 2 * k + 1
    g = {}
    for w in product((0, 1), repeat=r):
        cur = list(w)
        for _ in range(k):
            cur = [(rule >> (4 * cur[i] + 2 * cur[i + 1] + cur[i + 2])) & 1 for i in range(len(cur) - 2)]
        assert len(cur) == 1
        g[w] = cur[0]
    return g


def encode(x, b, pi):
    """E(x) = sum_i (1 + 2^pi x_i) 2^(b i)."""
    E = 0
    for i, xi in enumerate(x):
        E |= (1 + (xi << pi)) << (b * i)
    return E


def all_rows(N):
    return product((0, 1), repeat=N)

"""Independent grid count of chambers and output-affine classes.

u(x) = (T + 1/2 + R.x)/q with integers T in [0,q), R in [0,q)^n. Every such u is generic
(2(T+R.x)+1 is odd, never divisible by 2q). F(x) = floor(u(x)) computed exactly in integers.
Chamber key: F minus the integer affine function agreeing with F at 0 and each e_i.
Class key: f = F mod 2 XOR the GF(2)-affine function agreeing at 0 and each e_i.
Also checks: each class is hit by at most 2 chambers, and if 2, they are antipodal.
Usage: python3 grid_count.py n q
"""
import sys, itertools
import numpy as np

n = int(sys.argv[1]); q = int(sys.argv[2])
V = np.array(list(itertools.product([0, 1], repeat=n)), dtype=np.int64)  # 2^n x n
nv = len(V)
unit_idx = [0] + [int(''.join('1' if k == i else '0' for k in range(n)), 2) for i in range(n)]

def keys(F):
    # F: N x nv integer array
    F0 = F[:, [0]]
    d = F[:, unit_idx[1:]] - F0          # N x n
    m = F0 + d @ V.T                     # N x nv
    ch = F - m
    f = F & 1
    f0 = f[:, [0]]
    b = f[:, unit_idx[1:]] ^ f0
    aff = (f0 + b @ V.T) & 1
    cl = f ^ aff
    return ch, cl

def anti(F):
    return -F - 1

chambers = {}
classes = {}
Ts = np.arange(q, dtype=np.int64)
# iterate over R in chunks
Rall = itertools.product(range(q), repeat=n)
chunk = 200000 // q + 1
while True:
    Rs = list(itertools.islice(Rall, chunk))
    if not Rs:
        break
    Rs = np.array(Rs, dtype=np.int64)
    N = (Ts[:, None, None] + (Rs @ V.T)[None, :, :]).reshape(-1, nv)
    F = np.floor_divide(2 * N + 1, 2 * q)
    ch, cl = keys(F)
    cha, _ = keys(anti(F))
    for c, ca, k in zip(map(bytes, ch.astype(np.int16)), map(bytes, cha.astype(np.int16)),
                        map(bytes, cl.astype(np.int8))):
        if c not in chambers:
            chambers[c] = ca
            classes.setdefault(k, set()).add(c)

R = len(chambers)
bad = 0
selfanti = sum(1 for c, ca in chambers.items() if c == ca)
for k, cs in classes.items():
    cs = list(cs)
    if len(cs) > 2 or (len(cs) == 2 and chambers[cs[0]] != cs[1]):
        bad += 1
closed = all(ca in chambers for ca in chambers.values())
print(f"n={n} q={q} chambers={R} classes={len(classes)} (R+1)/2={(R+1)/2} "
      f"self_antipodal={selfanti} antipode_closed={closed} bad_classes={bad} "
      f"BLF=2^n*classes*2={2**n*2*len(classes)}")

from seeds_lift import lift
for (p, l) in [(3, 4), (5, 4), (3, 5)]:
    R = lift(p, l)
    print(f"lift p={p} l={l} r={R['r']} s={R['s']}: det_ok={R['det_ok']}, (A^-1)_0s={R['Ainv0s']}, "
          f"log2 (A^-1)_0s={float(R['Ainv0s']).__format__('.4e')}, P/r={float(R['bound']):.4e}, ok={R['ok']}, max|beta|={R['maxbeta']}, doubling={R['doubling']}", flush=True)

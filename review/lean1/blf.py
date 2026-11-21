import itertools, sys
def count(n, J):
    V = 1 << n
    seen = set()
    for j in range(J + 1):
        M = 1 << (j + 1)
        for a in itertools.product(range(M), repeat=n):
            s = [sum(a[i] for i in range(n) if x >> i & 1) for x in range(V)]
            for K in range(M):
                seen.add(sum(1 << x for x in range(V) if ((s[x] + K) % M) >> j & 1))
    return len(seen)
for n, J in [(1, 3), (2, 3), (3, 4), (4, 3)]:
    print(n, J, count(n, J))

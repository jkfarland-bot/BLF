import itertools, sys
def verts(n): return [tuple((k>>i)&1 for i in range(n)) for k in range(2**n)]
def tt(n,fn): return tuple(fn(x) for x in verts(n))
def blf(n,J):
    V=verts(n); S=set()
    for j in range(J+1):
        M=2**(j+1)
        for K in range(M):
            for a in itertools.product(range(M),repeat=n):
                S.add(tuple(((K+sum(ai*xi for ai,xi in zip(a,x)))>>j)&1 for x in V))
    return S
def thr(n,R):
    V=verts(n); S=set()
    for w in itertools.product(range(-R,R+1),repeat=n):
        for w0 in range(-n*R-1,n*R+2):
            S.add(tuple(int(w0+sum(a*b for a,b in zip(w,x))>0) for x in V))
    return S
def aff(n):
    V=verts(n)
    return [tuple((c+sum(bi*xi for bi,xi in zip(b,x)))%2 for x in V) for c in (0,1) for b in itertools.product((0,1),repeat=n)]
def txa(T,A): return {tuple(p^q for p,q in zip(t,a)) for t in T for a in A}
for n,J,R in [(3,4,4),(4,3,5)]:
    B=blf(n,J); T=thr(n,R); A=aff(n); X=txa(T,A)
    print(f"n={n}: |BLF|={len(B)} |thr|={len(T)} |aff|={len(A)} |TXA|={len(X)} TXA<=BLF {X<=B} |BLF-TXA|={len(B-X)}")
    if n==4:
        g=tt(4,lambda x:(sum(x)>>1)&1)
        G={tuple(p^q for p,q in zip(g,a)) for a in A}
        print(" bit1-sum translates:",len(G)," BLF-TXA == translates:",(B-X)==G," translates & TXA:",len(G&X))
# also larger threshold range to make sure thresholds complete
print("thr4 R=7:",len(thr(4,7)))

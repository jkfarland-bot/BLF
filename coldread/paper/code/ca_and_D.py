import itertools, math
# CA: BLF(3) via bit 3 of K + a.x with K,a in [0,16)
blf=set()
for K,a1,a2,a3 in itertools.product(range(16),repeat=4):
    T=0
    for l,c,r in itertools.product((0,1),repeat=3):
        idx=4*l+2*c+r
        if ((K+a1*l+a2*c+a3*r)>>3)&1: T|=1<<idx
    blf.add(T)
print("BLF(3) =",len(blf))
def refl(R): return sum(((R>>(4*l+2*c+r))&1)<<(4*r+2*c+l) for l,c,r in itertools.product((0,1),repeat=3))
def comp(R): return sum((1-((R>>(7-i))&1))<<i for i in range(8))
seen=set(); good=[]; bad=[]
for R in range(256):
    if R in seen: continue
    orb={R,refl(R),comp(R),comp(refl(R))}; seen|=orb
    ins=[x in blf for x in orb]; assert all(ins) or not any(ins)
    (good if ins[0] else bad).append(min(orb))
print(len(good)+len(bad),len(good),len(bad),sorted(bad), 110 in blf)
# D_n by Bareiss
def det(M):
    M=[row[:] for row in M]; k=len(M); s=1; prev=1
    for i in range(k):
        p=next((r for r in range(i,k) if M[r][i]),None)
        if p is None: return 0
        if p!=i: M[i],M[p]=M[p],M[i]; s=-s
        for r in range(i+1,k):
            for c in range(i+1,k):
                M[r][c]=(M[r][c]*M[i][i]-M[r][i]*M[i][c])//prev
        prev=M[i][i]
    return s*M[k-1][k-1]
for n in range(1,5):
    V=[[1]+[(x>>i)&1 for i in range(n)] for x in range(2**n)]
    D=0; S2=0; nb=0
    for B in itertools.combinations(V,n+1):
        d=det(list(map(list,B))); D+=abs(d); S2+=d*d; nb+= d!=0
    m=2**n
    print(n,"bases",nb,"D",D,"sum det^2",S2,"m^d/4^n",m**(n+1)//4**n,"bound",m**(n+1)/(2**n*math.sqrt(math.factorial(n+1))))

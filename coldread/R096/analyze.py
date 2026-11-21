# Cold read R096 analysis: closures, classes, LP thresholds (n<=4), NBC region counts, CA.
import sys, itertools
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog

def affs(n):
    N=1<<n; out=[]
    for c in (0,1):
        for s in range(N):
            t=0
            for x in range(N):
                if c ^ (bin(x&s).count('1')&1): t|=1<<x
            out.append(t)
    return out
def canon(t,A): return min(t^a for a in A)
def perm_table(t,n,p):  # g(x) = f(x permuted): g(x) = f(y) with y_{p[i]} = x_i
    N=1<<n; r=0
    for x in range(N):
        y=0
        for i in range(n):
            if (x>>i)&1: y|=1<<p[i]
        if (t>>y)&1: r|=1<<x
    return r
def comp_table(t,n,i):
    N=1<<n; r=0
    for x in range(N):
        if (t>>(x^(1<<i)))&1: r|=1<<x
    return r
def gens(n):
    G=[]
    if n>=2:
        G.append(lambda t: perm_table(t,n,[1,0]+list(range(2,n))))
        G.append(lambda t: perm_table(t,n,[(i+1)%n for i in range(n)]))
    G.append(lambda t: comp_table(t,n,0))
    return G
def closure(S,n,post=lambda t:t):
    S=set(post(t) for t in S); st=list(S); G=gens(n)
    while st:
        t=st.pop()
        for g in G:
            u=post(g(t))
            if u not in S: S.add(u); st.append(u)
    return S
def orbits(S,n,post):
    S=set(S); res=[]
    while S:
        t=next(iter(S)); o=closure([t],n,post); res.append(o); S-=o
    return res

# ---- NBC count of regions of central arrangement with normals (1,x) ----
P=2147483647
def reduce_vec(v,basis):  # basis: list of (pivot, vec) mod P
    v=list(v)
    for piv,b in basis:
        if v[piv]%P:
            c=v[piv]*pow(b[piv],P-2,P)%P
            v=[(vi-c*bi)%P for vi,bi in zip(v,b)]
    return v
def add_basis(basis,v):
    v=reduce_vec(v,basis); piv=next((i for i,x in enumerate(v) if x),None)
    return None if piv is None else basis+[(piv,v)]
def nbc_regions(n):
    vecs=[tuple([1]+[(x>>i)&1 for i in range(n)]) for x in range(1<<n)]
    cnt=0
    def dfs(mn,basis):
        nonlocal cnt; cnt+=1
        for s in range(mn):
            nb=add_basis(basis,vecs[s])
            if nb is None: continue
            if any(not any(reduce_vec(vecs[e],nb)) for e in range(s)): continue
            dfs(s,nb)
    dfs(len(vecs),[]); return cnt

# ---- LP thresholds ----
def lp_thresholds(n):
    N=1<<n; X=np.array([[1]+[(x>>i)&1 for i in range(n)] for x in range(N)],float)
    out=set()
    for t in range(1<<N):
        s=np.array([1 if (t>>x)&1 else -1 for x in range(N)],float)
        A=-(s[:,None]*X); b=-np.ones(N)
        r=linprog(np.zeros(n+1),A_ub=A,b_ub=b,bounds=[(None,None)]*(n+1),method='highs')
        if r.status==0:
            y=[Fraction(v).limit_denominator(10**6) for v in r.x]
            ok=all((sum(y[j]*X[x][j] for j in range(n+1))>0)==bool((t>>x)&1) for x in range(N))
            if not ok:  # exact repair: scale and round
                y=[Fraction(round(v*1000)) for v in r.x]
                ok=all((sum(y[j]*int(X[x][j]) for j in range(n+1))>0)==bool((t>>x)&1) for x in range(N))
            assert ok, t
            out.add(t)
    return out

def readset(fn): return set(int(l) for l in open(fn))

if __name__=='__main__':
    grids={1:3,2:7,3:13,4:27,5:55}
    nmax=int(sys.argv[1])
    for n in range(1,nmax+1):
        A=affs(n); N=1<<n; c=lambda t:canon(t,A)
        reg=nbc_regions(n)
        thr=closure(readset(f'thr_n{n}.txt'),n)
        line=f'n={n}: NBC regions={reg}, folded thresholds closed={len(thr)}'
        if n<=4:
            lp=lp_thresholds(n); line+=f', LP thresholds={len(lp)}, LP==folded:{lp==thr}'
        print(line)
        tcls=set(c(t) for t in thr)
        bcls=closure(readset(f'blf_n{n}_q{grids[n]}.txt'),n,c)
        extra=bcls-tcls
        print(f'   thr XOR aff classes={len(tcls)}, BLF classes={len(bcls)}, thr classes inside BLF: {tcls<=bcls}, extra={len(extra)}, BLF tables={len(bcls)*2*N}, thrXORaff tables={len(tcls)*2*N}')
        ob=orbits(extra,n,c); print('   extra orbits sizes:',sorted(len(o) for o in ob))
        if n==4:
            g=sum(1<<x for x in range(N) if (bin(x).count('1')>>1)&1)
            print('   extra class == class of bit1(x1+..+x4):', extra=={c(g)})
        if n==5:
            g=sum(1<<x for x in range(N) if (bin(x).count('1')>>1)&1)
            print('   n=5 popcount bit1 class in extra:', c(g) in extra)
        if n==3:
            blf3=set()
            for k in bcls:
                for a in A: blf3.add(k^a)
            # CA classes
            def f_of(R): return R  # bit 4l+2c+r of R; table index x = x1 + 2x2 + 4x3 with x1=r,x2=c,x3=l
            def refl(R): return sum(((R>>(4*(i&1)+2*((i>>1)&1)+((i>>2)&1)))&1)<<i for i in range(8))
            def conj(R): return sum((1-((R>>(7-i))&1))<<i for i in range(8))
            seen=set(); classes=[]
            for R in range(256):
                if R in seen: continue
                cl={R,refl(R),conj(R),refl(conj(R))}; seen|=cl; classes.append(sorted(cl))
            mixed=[cl for cl in classes if len(set(r in blf3 for r in cl))>1]
            bad=[cl[0] for cl in classes if cl[0] not in blf3]
            print(f'   |BLF(3)|={len(blf3)}; CA classes={len(classes)}, BLF={len(classes)-len(bad)}, non-BLF={len(bad)}, mixed={len(mixed)}')
            print('   non-BLF minimal reps:',bad,'; rule 110 BLF:',110 in blf3)

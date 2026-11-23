# Check step (c) of the lower bound literally: with t_j = L^-j, H=(r+1)^(r+1), L=H+2,
# every intersection point of the walls of a good B is passed by no other wall; and count
# sum_good |det A_B| versus the number of simple vertices among all B-vertices.
import itertools, sys
from fractions import Fraction as Fr

def rank(M):
    M=[[Fr(e) for e in row] for row in M]; rk=0; cols=len(M[0])
    for cidx in range(cols):
        p=next((i for i in range(rk,len(M)) if M[i][cidx]!=0),None)
        if p is None: continue
        M[rk],M[p]=M[p],M[rk]
        for i in range(len(M)):
            if i!=rk and M[i][cidx]!=0:
                f=M[i][cidx]/M[rk][cidx]; M[i]=[x-f*y for x,y in zip(M[i],M[rk])]
        rk+=1
    return rk
def solve(A,b):
    k=len(A); M=[[Fr(e) for e in A[i]]+[Fr(b[i])] for i in range(k)]
    for cidx in range(k):
        p=next(i for i in range(cidx,k) if M[i][cidx]!=0); M[cidx],M[p]=M[p],M[cidx]
        for i in range(k):
            if i!=cidx and M[i][cidx]!=0:
                f=M[i][cidx]/M[cidx][cidx]; M[i]=[x-f*y for x,y in zip(M[i],M[cidx])]
    return [M[i][k]/M[i][i] for i in range(k)]
def detf(A):
    k=len(A); M=[[Fr(e) for e in r] for r in A]; d=Fr(1)
    for cidx in range(k):
        p=next((i for i in range(cidx,k) if M[i][cidx]!=0),None)
        if p is None: return 0
        if p!=cidx: M[cidx],M[p]=M[p],M[cidx]; d=-d
        d*=M[cidx][cidx]
        for i in range(cidx+1,k):
            f=M[i][cidx]/M[cidx][cidx]; M[i]=[x-f*y for x,y in zip(M[i],M[cidx])]
    return int(d)
def run(n,k):
    r=n+1-k; H=(r+1)**(r+1); L=H+2
    t={j:Fr(1,L**j) for j in range(r,n+1)}
    pts=list(itertools.product((0,1),repeat=n))   # x = (x_1..x_n)
    a={x:(1,)+x[:r-1] for x in pts}
    c={x:sum(x[j-1]*t[j] for j in range(r,n+1)) for x in pts}
    v={x:(1,)+x for x in pts}
    goodmass=0; bad_simple_fail=0; vertset={}
    for B in itertools.combinations(pts,r):
        A=[a[x] for x in B]; D=detf(A)
        if D==0: continue
        rk=rank([v[x] for x in B])
        good = all(rank([v[x] for x in B]+[v[y]])>rk for y in pts if y not in B)
        ps=set()
        for N in itertools.product(range(abs(D)),repeat=r):
            z=tuple(e%1 for e in solve(A,[Fr(N[i])-c[B[i]] for i in range(r)]))
            ps.add(z)
        assert len(ps)==abs(D)
        for p in ps:
            through=[y for y in pts if (sum(ai*pi for ai,pi in zip(a[y],p))+c[y]).denominator==1]
            vertset[p]=len(through)
            if good and len(through)!=r: bad_simple_fail+=1
        if good: goodmass+=abs(D)
    simple=sum(1 for p,cnt in vertset.items() if cnt==r)
    print(f"n={n} k={k} r={r}: sum_good|det|={goodmass} simple_vertices={simple} vertices={len(vertset)} good-but-not-simple={bad_simple_fail}")
for n,k in [(2,1),(3,1),(3,2),(4,1),(4,2),(4,3)]:
    run(n,k)

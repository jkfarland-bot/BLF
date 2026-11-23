import itertools, math
from fractions import Fraction
def det(M):
    import copy; M=[r[:] for r in M]; k=len(M); s=1; prev=1
    for i in range(k):
        p=next((r for r in range(i,k) if M[r][i]),None)
        if p is None: return 0
        if p!=i: M[i],M[p]=M[p],M[i]; s=-s
        for r in range(i+1,k):
            for c in range(i+1,k): M[r][c]=(M[r][c]*M[i][i]-M[r][i]*M[i][c])//prev
        prev=M[i][i]
    return s*M[k-1][k-1]
for r in range(1,5):
    rows=[(1,)+t for t in itertools.product((1,-1),repeat=r-1)]
    N=0;E1=E2=E4=0
    for S in itertools.product(rows,repeat=r):
        z=abs(det([list(x) for x in S])); N+=1; E1+=z;E2+=z*z;E4+=z**4
    E1=Fraction(E1,N);E2=Fraction(E2,N);E4=Fraction(E4,N)
    hb=math.sqrt(math.factorial(r))*math.sqrt(2/((r+1)*(r+2)))
    print(r,"EZ",float(E1),"EZ2",E2,"r!",math.factorial(r),"EZ4",E4,"bound",math.factorial(r)*math.factorial(r+2)//2,"Holder",round(hb,4))

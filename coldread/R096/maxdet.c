/* Cold read R096: max |det| over square submatrices built from row sets.
   Delta_n: rows (1,x,s), x in {0,1}^n, s=+-1, size n+2.  WLOG (unimodular column ops:
   x_i -> 1-x_i is col_i -> col_0 - col_i; s -> -s is negating last column) the subset
   contains the row (1,0,...,0,+1); we fix it and choose the other n+1 rows.
   M_n(k): rows (1,x) with column k replaced by s, size n+1; full brute force,
   both allowing two rows with the same x (different s) and requiring distinct x. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll;
static ll det(ll a[8][8], int m){ /* Bareiss */
  ll A[8][8]; memcpy(A,a,sizeof(A)); ll prev=1; int sign=1;
  for(int k=0;k<m-1;k++){
    if(A[k][k]==0){int p=-1; for(int i=k+1;i<m;i++) if(A[i][k]){p=i;break;}
      if(p<0) return 0; for(int j=0;j<m;j++){ll t=A[k][j];A[k][j]=A[p][j];A[p][j]=t;} sign=-sign;}
    for(int i=k+1;i<m;i++) for(int j=k+1;j<m;j++) A[i][j]=(A[i][j]*A[k][k]-A[i][k]*A[k][j])/prev;
    prev=A[k][k];
  }
  return sign*A[m-1][m-1];
}
static int R, m, rows[200][8], xid[200], distinct; static ll best; static int pick[8];
static void rec(int start,int depth,int fixed){
  if(depth==m){ ll a[8][8]; for(int i=0;i<m;i++) for(int j=0;j<m;j++) a[i][j]=rows[pick[i]][j];
    ll d=llabs(det(a,m)); if(d>best) best=d; return; }
  for(int r=start;r<R;r++){
    if(distinct){int bad=0; for(int i=0;i<depth;i++) if(xid[pick[i]]==xid[r]) bad=1; if(bad) continue;}
    pick[depth]=r; rec(r+1,depth+1,fixed);
  }
}
int main(int argc,char**argv){
  int nmax=atoi(argv[1]);
  for(int n=0;n<=nmax;n++){
    /* Delta_n */
    R=0; for(int x=0;x<(1<<n);x++) for(int s=-1;s<=1;s+=2){ rows[R][0]=1; for(int i=0;i<n;i++) rows[R][1+i]=(x>>i)&1; rows[R][n+1]=s; xid[R]=x; R++; }
    /* put (1,0..0,+1) first: it is index 1 (x=0,s=+1) */
    m=n+2; best=0; distinct=0;
    { int tmp[8]; memcpy(tmp,rows[1],sizeof tmp); memcpy(rows[1],rows[0],sizeof tmp); memcpy(rows[0],tmp,sizeof tmp); int t=xid[0];xid[0]=xid[1];xid[1]=t; }
    pick[0]=0; rec(1,1,1);
    printf("n=%d Delta_n=%lld\n",n,best); fflush(stdout);
    if(n==0) continue;
    for(int k=0;k<=1;k++) for(distinct=0;distinct<=1;distinct++){
      R=0; for(int x=0;x<(1<<n);x++){
        if(k>=1 && ((x>>(k-1))&1)) continue; /* x_k is overwritten: dedupe rows */
        for(int s=-1;s<=1;s+=2){ rows[R][0]=1; for(int i=0;i<n;i++) rows[R][1+i]=(x>>i)&1; rows[R][k]=s; xid[R]=x; R++; } }
      if(k>=1 && distinct){ /* distinct original x: row (..,s,..) comes from x with x_k=0 or 1; distinctness then
                               means the pair (rest of x, s) may repeat at most... handle by full set with x_k free */
        R=0; for(int x=0;x<(1<<n);x++) for(int s=-1;s<=1;s+=2){ rows[R][0]=1; for(int i=0;i<n;i++) rows[R][1+i]=(x>>i)&1; rows[R][k]=s; xid[R]=x; R++; }
      }
      m=n+1; best=0; rec(0,0,0);
      printf("n=%d M(k=%d, %s)=%lld\n",n,k,distinct?"distinct x":"repeats ok",best); fflush(stdout);
    }
  }
}

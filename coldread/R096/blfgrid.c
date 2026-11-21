/* BLF classes on an odd grid: u = t + r.x with t = (2K+1)/(2q), r_i = a_i/q.
   Folded: 0 <= a_1 <= ... <= a_n <= q/2 (permutations and complementations of inputs,
   r_i -> -r_i mod 1, map the grid to itself).  Prints canonical class reps
   (min truth table over XOR with all GF(2)-affine functions). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned long long u64;
int n,q,N; u64 aff[128]; int naff;
#define HS (1<<24)
u64 *H; char *used;
static void ins(u64 v){ u64 h=(v*0x9E3779B97F4A7C15ULL)>>40; while(used[h]){ if(H[h]==v) return; h=(h+1)&(HS-1);} used[h]=1; H[h]=v; }
int a[8];
static void go(int i,int lo){
  if(i==n){ for(int K=0;K<q;K++){ u64 tb=0; for(int x=0;x<N;x++){ long num=2*K+1; for(int j=0;j<n;j++) if((x>>j)&1) num+=2*a[j];
        long F=num/(2*q); if(F&1) tb|=1ULL<<x; }
      u64 c=tb; for(int k=0;k<naff;k++){u64 v=tb^aff[k]; if(v<c)c=v;} ins(c);} return; }
  for(int v=lo; 2*v<=q; v++){ a[i]=v; go(i+1,v); }
}
int main(int argc,char**argv){ n=atoi(argv[1]); q=atoi(argv[2]); N=1<<n;
  u64 mask = (N==64)?~0ULL:((1ULL<<N)-1);
  naff=0; for(int c=0;c<2;c++) for(int s=0;s<N;s++){ u64 t=0; for(int x=0;x<N;x++){ int b=c^(__builtin_popcount(x&s)&1); if(b) t|=1ULL<<x;} aff[naff++]=t&mask; }
  H=malloc(sizeof(u64)*HS); used=calloc(HS,1); go(0,0);
  for(long h=0;h<HS;h++) if(used[h]) printf("%llu\n",H[h]);
}

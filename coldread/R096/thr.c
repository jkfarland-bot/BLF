/* Threshold functions [Y0 + Y.x > 0], folded: 0<=Y1<=...<=Yn<=M, |Y0|<=(n+1)M. Prints distinct tables. */
#include <stdio.h>
#include <stdlib.h>
typedef unsigned long long u64;
int n,M,N; int Y[8];
#define HS (1<<24)
u64 *H; char *used;
static void ins(u64 v){ u64 h=(v*0x9E3779B97F4A7C15ULL)>>40; while(used[h]){ if(H[h]==v) return; h=(h+1)&(HS-1);} used[h]=1; H[h]=v; }
static void go(int i,int lo){
  if(i==n){ for(int y0=-(n+1)*M;y0<=(n+1)*M;y0++){ u64 t=0; for(int x=0;x<N;x++){ int s=y0; for(int j=0;j<n;j++) if((x>>j)&1) s+=Y[j]; if(s>0) t|=1ULL<<x; } ins(t);} return; }
  for(int v=lo;v<=M;v++){Y[i]=v; go(i+1,v);}
}
int main(int argc,char**argv){ n=atoi(argv[1]); M=atoi(argv[2]); N=1<<n; H=malloc(sizeof(u64)*HS); used=calloc(HS,1); go(0,0);
  for(long h=0;h<HS;h++) if(used[h]) printf("%llu\n",H[h]); }

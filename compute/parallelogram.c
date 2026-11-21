/* Parallelogram test. Counts integer G on {0,1}^n with G(0) = G(e_i) = 0 and
   |G(x) + G(y) - G(z) - G(w)| <= 1 for every x + y = z + w (cube vertices, {x,y} != {z,w}).
   Every floor vector of an affine u (normalized by subtracting its integer affine interpolant) satisfies
   these: G(x)+G(y)-G(z)-G(w) = -(a(x)+a(y)-a(z)-a(w)) with a = frac in [0,1), so it lies in (-2, 2).
   Result: the count equals R_n for n <= 6 (1, 3, 25, 647, 59493, 21238195).
   usage: parallelogram n */
/* n=4: count G (G(0)=G(e_i)=0) satisfying all 4-term relations v_x+v_y=v_z+v_w (|G(x)+G(y)-G(z)-G(w)| <= 1),
   by DFS over vertices in order of weight with pruning. */
#include <stdio.h>
#include <stdlib.h>
int n,N; int G[64]; int order[64]; int no=0; long cnt=0;
int rel[3000000][4]; int nr=0; int relmax[3000000];
int pos[64]; int start[66]; int byk[3000000];
#include <string.h>
static unsigned char *cls; long ncls=0;
void dfs(int k){
  if(k==no){ cnt++; return;
  }
  int x=order[k]; int w=__builtin_popcount(x);
  for(int v=-(w-1); v<=w-1; v++){ G[x]=v; int ok=1;
    for(int ii=start[k];ii<start[k+1]&&ok;ii++){ int r=byk[ii]; int s=G[rel[r][0]]+G[rel[r][1]]-G[rel[r][2]]-G[rel[r][3]]; if(s>1||s<-1) ok=0; }
    if(ok) dfs(k+1); }
}
int main(int c,char**v){ n=atoi(v[1]); N=1<<n; cls=0;
  for(int w=2;w<=n;w++) for(int x=0;x<N;x++) if(__builtin_popcount(x)==w){pos[x]=no; order[no++]=x;}
  for(int x=0;x<N;x++) if(__builtin_popcount(x)<2) pos[x]=-1;
  /* relations x+y=z+w as integer vectors and {x,y} != {z,w}, with 1+1=1+1 automatically */
  for(int x=0;x<N;x++)for(int y=x;y<N;y++)for(int z=0;z<N;z++)for(int w=z;w<N;w++){
    if(z<x || (z==x)) continue; /* z>x canonical */
    int ok=1; for(int i=0;i<n;i++) if(((x>>i)&1)+((y>>i)&1)!=((z>>i)&1)+((w>>i)&1)) ok=0;
    if(!ok) continue; if((x==z&&y==w)||(x==w&&y==z)) continue;
    int m=-1; int vs[4]={x,y,z,w}; for(int t=0;t<4;t++) if(pos[vs[t]]>m) m=pos[vs[t]];
    if(m<0) continue; rel[nr][0]=x;rel[nr][1]=y;rel[nr][2]=z;rel[nr][3]=w; relmax[nr]=m; nr++; }
  for(int r=0;r<nr;r++) start[relmax[r]+1]++;
  for(int k=0;k<no;k++) start[k+1]+=start[k];
  { int fill[64]={0}; for(int r=0;r<nr;r++){ int k=relmax[r]; byk[start[k]+fill[k]++]=r; } }
  for(int x=0;x<N;x++) G[x]=0;
  dfs(0); printf("n=%d relations=%d G=%ld classes=%ld\n",n,nr,cnt,ncls); }

/* Independent check for n<=5: threshold functions (sorted nonnegative weights <= W, then closed
   under the hyperoctahedral group), TXA classes, BLF classes at bit n (grid 2^n, K,a in [0,2^n)),
   extra classes and their orbit sizes. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int n,m;
static uint32_t normalize(uint32_t T){int f0=T&1;uint32_t out=0;
  for(int x=0;x<m;x++){int v=(T>>x)&1,aff=f0;for(int i=0;i<n;i++)if((x>>i)&1)aff^=((T>>(1<<i))&1)^f0;out|=(uint32_t)(v^aff)<<x;}return out;}
static int perms[120][5],np=0;
static void genp(int*p,int k){if(k==n){for(int i=0;i<n;i++)perms[np][i]=p[i];np++;return;}
  for(int i=k;i<n;i++){int t=p[k];p[k]=p[i];p[i]=t;genp(p,k+1);t=p[k];p[k]=p[i];p[i]=t;}}
static uint32_t act(uint32_t T,int pi,int c){uint32_t out=0;
  for(int x=0;x<m;x++){int y=0;for(int i=0;i<n;i++){int b=((x>>i)&1)^((c>>i)&1);if(b)y|=1<<perms[pi][i];}
    out|=(uint32_t)((T>>y)&1)<<x;}return out;}
static uint8_t *bm_new(void){return calloc(((size_t)1<<(m>32?32:m))/8+1,1);}
#define GET(b,N) ((b[(N)>>3]>>((N)&7))&1)
#define SET(b,N) (b[(N)>>3]|=1<<((N)&7))
int main(int argc,char**argv){n=atoi(argv[1]);int W=atoi(argv[2]);m=1<<n;
  int p[5]={0,1,2,3,4};genp(p,0);
  uint8_t *thr=bm_new(),*txa=bm_new(),*blf=bm_new(); /* thr indexed by full table (m<=32) */
  int w[6];long nthr=0;
  /* sorted weights 0<=w1<=..<=wn<=W, w0 in [-(n+1)W-1,(n+1)W+1] ; tables then closed under group */
  uint32_t *list=malloc(sizeof(uint32_t)*4000000);long nl=0;
  uint8_t *tmp=bm_new();
  for(int i=0;i<n;i++)w[i+1]=0;
  while(1){
    for(int w0=-(n+1)*W-1;w0<=(n+1)*W+1;w0++){uint32_t T=0;
      for(int x=0;x<m;x++){long s=w0;for(int i=0;i<n;i++)if((x>>i)&1)s+=w[i+1];if(s>0)T|=(uint32_t)1<<x;}
      if(!GET(tmp,T)){SET(tmp,T);list[nl++]=T;}}
    int k=1;while(k<=n){w[k]++;int ok=1;for(int t=k+1;t<=n;t++)if(w[k]>w[t])ok=0; if(w[k]<=W&&ok)break;
      /* reset */ w[k]=0;k++;}
    if(k>n)break;
    for(int t=1;t<k;t++)w[t]=0;
  }
  for(long i=0;i<nl;i++)for(int pi=0;pi<np;pi++)for(int c=0;c<m;c++){uint32_t U=act(list[i],pi,c);
    if(!GET(thr,U)){SET(thr,U);nthr++;SET(txa,normalize(U));}}
  long ntxa=0;for(uint64_t N=0;N<((uint64_t)1<<m);N++)if(GET(txa,N))ntxa++;
  /* BLF classes at bit n */
  long idx[7]={0};long nb=0;uint64_t q=1ull<<n;
  while(1){uint32_t T=0;for(int x=0;x<m;x++){long s=idx[0];for(int i=0;i<n;i++)if((x>>i)&1)s+=idx[i+1];T|=(uint32_t)((s>>n)&1)<<x;}
    uint32_t N=normalize(T);if(!GET(blf,N)){SET(blf,N);nb++;}
    int pp=0;while(pp<=n){idx[pp]++;if((uint64_t)idx[pp]<q)break;idx[pp]=0;pp++;}if(pp>n)break;}
  long bad=0,extra=0;
  for(uint64_t N=0;N<((uint64_t)1<<m);N++){if(GET(txa,N)&&!GET(blf,N))bad++;}
  printf("n=%d W=%d thresholds=%ld txa_classes=%ld blf_classes=%ld txa_not_blf=%ld\n",n,W,nthr,ntxa,nb,bad);
  uint8_t *done=bm_new();int sizes[64];int ns=0;
  for(uint64_t N=0;N<((uint64_t)1<<m);N++){if(GET(blf,N)&&!GET(txa,N)&&!GET(done,N)){extra++;
     long sz=0;/* orbit */
     for(int pi=0;pi<np;pi++)for(int c=0;c<m;c++){uint32_t U=normalize(act((uint32_t)N,pi,c));if(!GET(done,U)){SET(done,U);sz++;}}
     sizes[ns++]=sz;} }
  long tot=0;printf("extra orbits=%d sizes:",ns);for(int i=0;i<ns;i++){printf(" %d",sizes[i]);tot+=sizes[i];}printf(" total=%ld\n",tot);
  uint8_t *d2=bm_new();int all=0,txo=0;
  for(uint64_t N=0;N<((uint64_t)1<<m);N++){if(GET(blf,N)&&!GET(d2,N)){all++;if(GET(txa,N))txo++;
     for(int pi=0;pi<np;pi++)for(int c=0;c<m;c++){uint32_t U=normalize(act((uint32_t)N,pi,c));SET(d2,U);}}}
  printf("all BLF class orbits=%d (TXA orbits %d)\n",all,txo);
  return 0;}

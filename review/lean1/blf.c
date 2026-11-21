#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc,char**argv){
  int n=atoi(argv[1]), J=atoi(argv[2]);
  int V=1<<n; uint64_t F=1ULL<<V;
  unsigned char *seen=calloc(F,1);
  for(int j=0;j<=J;j++){
    long M=1L<<(j+1);
    long a[8]={0};
    long tot=1; for(int i=0;i<n;i++) tot*=M;
    for(long c=0;c<tot;c++){
      long t=c; for(int i=0;i<n;i++){a[i]=t%M;t/=M;}
      long s[64];
      for(int x=0;x<V;x++){long v=0;for(int i=0;i<n;i++) if(x>>i&1) v+=a[i]; s[x]=v;}
      for(long K=0;K<M;K++){
        uint64_t tt=0;
        for(int x=0;x<V;x++){ long N=(s[x]+K)%M; if((N>>j)&1) tt|=1ULL<<x; }
        seen[tt]=1;
      }
    }
    long cnt=0; for(uint64_t f=0;f<F;f++) cnt+=seen[f];
    printf("n=%d j<=%d count=%ld\n",n,j,cnt); fflush(stdout);
  }
}

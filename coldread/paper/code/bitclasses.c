/* Independent check: number of output-affine classes reached at bit j, n <= 5.
   Classes are normalized truth tables (XOR with the affine fn agreeing at 0 and e_i).
   At fixed j the reached set is closed under affine XOR, so K, a_i in [0, 2^j) suffice. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int n, m;
static uint32_t normalize(uint32_t T){
  int f0 = T & 1; uint32_t out=0;
  for(int x=0;x<m;x++){
    int v = (T>>x)&1; int aff=f0;
    for(int i=0;i<n;i++) if((x>>i)&1) aff ^= ((T>>(1<<i))&1) ^ f0;
    out |= (uint32_t)(v^aff)<<x;
  }
  return out;
}
int main(int argc,char**argv){
  n=atoi(argv[1]); int j=atoi(argv[2]); m=1<<n;
  uint64_t q=1ull<<j; size_t nb = (size_t)1<<(m>32?32:m);
  uint8_t *seen = calloc(nb/8+1,1); long cnt=0;
  long a[8]; int np=n+1; long idx[8]={0};
  while(1){
    uint32_t T=0;
    for(int x=0;x<m;x++){ long s=idx[0]; for(int i=0;i<n;i++) if((x>>i)&1) s+=idx[i+1];
      T |= (uint32_t)((s>>j)&1)<<x; }
    uint32_t N=normalize(T);
    if(!(seen[N>>3]&(1<<(N&7)))){seen[N>>3]|=1<<(N&7);cnt++;}
    int p=0; while(p<np){ idx[p]++; if((uint64_t)idx[p]<q) break; idx[p]=0; p++; } if(p==np) break;
  }
  printf("n=%d j=%d classes=%ld\n",n,j,cnt);
  (void)a; return 0;
}

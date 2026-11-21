/* Output-affine classes of BLF(n) (universal grid, folded + closure, hash set) and their orbits
   under the hyperoctahedral group (input permutations and complementations). usage: orbits n q */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int n, N;
static uint64_t canon(uint64_t T){int f0=T&1;uint64_t A=0;for(int x=0;x<N;x++){int b=f0;for(int i=0;i<n;i++)if(x>>i&1)b^=(int)((T>>(1<<i))&1)^f0;A|=(uint64_t)b<<x;}return T^A;}
static uint64_t swp(uint64_t T,int i,int j){uint64_t R=0;for(int x=0;x<N;x++){int bi=x>>i&1,bj=x>>j&1;int y=x&~((1<<i)|(1<<j));y|=bi<<j;y|=bj<<i;R|=((T>>x)&1)<<y;}return R;}
static uint64_t flp(uint64_t T,int i){uint64_t R=0;for(int x=0;x<N;x++)R|=((T>>x)&1)<<(x^(1<<i));return R;}
#define HB 25
static uint64_t *H; static uint8_t *mark; static uint64_t *Q; static long qn=0;
static long find(uint64_t k){uint64_t key=k+1;uint64_t p=(key*0x9E3779B97F4A7C15ULL)>>(64-HB);while(H[p]&&H[p]!=key)p=(p+1)&((1UL<<HB)-1);return (long)p;}
static void add(uint64_t T){long p=find(T);if(!H[p]){H[p]=T+1;Q[qn++]=T;}}
static long q; static long a[8];
static void rec(int i,long lo){ if(i==n){long s[64];for(int x=0;x<N;x++){long v=0;for(int k=0;k<n;k++)if(x>>k&1)v+=a[k];s[x]=v;}
  for(long K=0;K<q;K++){uint64_t T=0;for(int x=0;x<N;x++)T|=(uint64_t)(((K+s[x])/q)&1)<<x;add(canon(T));}return;}
  for(long v=lo;v<=q/2;v++){a[i]=v;rec(i+1,v);} }
int main(int c,char**v){n=atoi(v[1]);q=atol(v[2]);N=1<<n;H=calloc(1UL<<HB,8);mark=calloc(1UL<<HB,1);Q=malloc(sizeof(uint64_t)*(1UL<<HB));
  rec(0,0);
  for(long h=0;h<qn;h++){uint64_t T=Q[h];for(int i=0;i+1<n;i++)add(canon(swp(T,i,i+1)));if(n)add(canon(flp(T,0)));}
  long orbits=0; uint64_t *st=malloc(sizeof(uint64_t)*(1UL<<HB));
  for(long h=0;h<qn;h++){long p=find(Q[h]); if(mark[p])continue; orbits++; long sp=0; st[sp++]=Q[h]; mark[p]=1;
    while(sp){uint64_t U=st[--sp]; uint64_t nb[8];int k=0;for(int i=0;i+1<n;i++)nb[k++]=canon(swp(U,i,i+1));if(n)nb[k++]=canon(flp(U,0));
      for(int e=0;e<k;e++){long pp=find(nb[e]); if(!mark[pp]){mark[pp]=1;st[sp++]=nb[e];}}}}
  printf("n=%d q=%ld classes=%ld orbits=%ld tables=%ld\n",n,q,qn,orbits,qn<<(n+1)); return 0;}

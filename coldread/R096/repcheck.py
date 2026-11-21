import sys; sys.argv=['x','0']; exec(open('analyze.py').read().split("if __name__")[0])
A4=affs(4); g=sum(1<<x for x in range(16) if (bin(x).count('1')>>1)&1); print(hex(canon(g,A4)))
n=5; A=affs(5); c=lambda t:canon(t,A)
thr=closure(readset('thr_n5.txt'),5); tc=set(c(t) for t in thr)
b=closure(readset('blf_n5_q55.txt'),5,c); ob=orbits(b-tc,5,c)
mine=sorted((min(o),len(o)) for o in ob)
theirs=[0x3ffcfcc0,0x1ff8f8e0,0x177ee8e8,0x18088e8,0x180e8e8,0x3c0c0e8,0x180a8e8,0x177ee880,0x380c0e8,0x33e3ee8,0x177e7ee8,0x18080e8,0x37e7ee8,0x17e7ee8,0x77e7ee8]
sz=[5,80,80,320,320,480,960,160,640,160,1,32,160,320,32]
print(sorted(zip(theirs,sz))==mine)
print([(hex(a),b) for a,b in mine])
# their convention may differ in bit order: test reversal x -> complement index
def rev(t,N): return sum(((t>>(N-1-x))&1)<<x for x in range(N))
print(hex(rev(0x7ee8,16)), hex(canon(rev(0x7ee8,16),A4)))
print(all(any(o for o in ob if canon(t,A) in o and len(o)==s) for t,s in zip(theirs,sz)))
print(hex(canon(0x7ee8,A4)))
print(len({next(i for i,o in enumerate(ob) if canon(t,A) in o) for t in theirs}))

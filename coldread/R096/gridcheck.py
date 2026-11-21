import subprocess,sys
sys.argv=['x','0']; exec(open('analyze.py').read().split("if __name__")[0])
for n,qs in [(3,[5,7,9,11,13,21]),(4,[9,13,17,21,25,27,35,41]),(5,[25,35,45,51,55,67])]:
    A=affs(n); c=lambda t:canon(t,A)
    for q in qs:
        out=subprocess.run(['./blfgrid',str(n),str(q)],capture_output=True,text=True).stdout.split()
        print(n,q,len(closure(set(map(int,out)),n,c)))

import itertools, sys
sys.path.insert(0, '/home/claude/vscratch3')
from indep import truth_table, is_blf_exact, square_ok_some_beta, rule
def two_mixed(x, outer=111, inner=110):
    s1 = [rule(inner, x[i], x[i+1], x[i+2]) for i in range(3)]
    return rule(outer, *s1)
f = truth_table(lambda x: two_mixed(x), 5)
def sq(f, i, k, p):
    pi = p | (1 << i); pk = p | (1 << k); pik = pi | (1 << k)
    return [((f[p]^f[pk]^bk)+(f[pk]^f[pik]^bi)) == ((f[p]^f[pi]^bi)+(f[pi]^f[pik]^bk)) for bi,bk in itertools.product((0,1),repeat=2)]
print("outer 111, inner 110: BLF", is_blf_exact(f, 5), "; proof squares jointly satisfiable:", any(a and b for a,b in zip(sq(f,3,4,0), sq(f,3,4,2))))

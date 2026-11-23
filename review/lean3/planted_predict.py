import itertools, sys
sys.path.insert(0, '/home/claude/vscratch3')
from indep import truth_table, is_blf_exact, square_ok_some_beta, rule, steps
def r(R): return lambda l,c,r_: rule(R,l,c,r_)
for R in (110, 111):
    two = truth_table(lambda x: steps(list(x), 2, r(R))[0], 5)
    print("rule", R, "two steps BLF:", is_blf_exact(two, 5), "square ok some beta:", square_ok_some_beta(two, 5))
    # the specific two squares used in Rule110.lean
    def sq(f, i, k, p):
        pi = p | (1 << i); pk = p | (1 << k); pik = pi | (1 << k)
        return [((f[p]^f[pk]^bk)+(f[pk]^f[pik]^bi)) == ((f[p]^f[pi]^bi)+(f[pi]^f[pik]^bk)) for bi,bk in itertools.product((0,1),repeat=2)]
    a = sq(two, 3, 4, 0); b = sq(two, 3, 4, 2)
    print("  squares used in proof jointly satisfiable:", any(x and y for x,y in zip(a,b)))

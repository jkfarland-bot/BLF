# Cold read of PROOF_R096.md (21 Nov 2026)

Reader: independent cold reader (Claude Opus 5.5). Read PROOF_R096.md against PROOF_R116.md (Proposition 1,
F1 to F3, Lemma 2). All code here is new, written from scratch in /home/claude/coldread_R096/; nothing in
/home/claude/blf was modified or reused (results/runs_21nov.txt was only read for comparison).

## Verdict

**Proved with repairs.** Every statement is correct and every number in the table and in Sections 4 and 5
was reproduced by independent code, partly with different methods. The repairs are wording only: one
false intermediate claim in the proof of Lemma 4 (the LP feasible set is called a polytope, but it is
unbounded) whose fix is one added constraint, plus clarifications. No gap.

## Issues (numbered, with suggested wording)

**1. Lemma 4, the LP is not over a polytope (real but harmless error).** With only the constraints
t + r.x - delta >= F(x), t + r.x + delta <= F(x) + 1, delta <= 1, the feasible set is unbounded: letting
delta go to minus infinity loosens every constraint, and then (t, r) is unbounded too. The conclusion
survives (the set is a pointed polyhedron, since the rows (1, x, +-1) span R^(n+2), and the objective is
bounded above, so an optimal vertex exists), but the sentence as written is false. Simplest repair: add
delta >= 0. Suggested wording:

> Maximize delta subject to t + r.x - delta >= F(x), t + r.x + delta <= F(x) + 1 (all x) and delta >= 0.
> The feasible set is a nonempty polytope: it contains P x {0}, its projection to (t, r) lies in the
> closure of P, and adding the two constraints at any x gives delta <= 1/2.

**2. Lemma 4, the cap is never tight; the case "otherwise delta* = 1" is vacuous.** As noted, 2 delta <= 1
always, so delta <= 1 can never be active, and delta* = 1 is impossible. With the repair of Issue 1 the
only non-(1, x, +-1) row is delta >= 0, which is not tight at an optimum because delta* > 0. Suggested
wording to replace the two sentences starting "If the cap is not tight":

> At an optimal vertex delta* > 0, so delta >= 0 is not tight and the vertex solves n + 2 linearly
> independent tight constraints with rows (1, x, -+1) and integer right-hand sides F(x) or F(x) + 1. By
> Cramer, delta* = N / det with N an integer, nonzero because delta* > 0, and 0 < |det| <= Delta_n;
> hence delta* >= 1/Delta_n. (Rows (1, x, -1) and (1, x, +1) for the same x may both occur; they are
> both in the row set defining Delta_n.)

The rounding step is correct as written: each of the n + 1 coordinates moves by at most 1/(2q) (the
spacing of Z/q and of (2Z + 1)/(2q) is 1/q), so t + r.x moves by at most (1 + |x|)/(2q) <= (n+1)/(2q),
which is strictly less than 1/Delta_n <= delta* exactly when q > (n+1) Delta_n / 2. Strictness is right
and needed (the rounded point must satisfy the strict inequalities of P).

**3. Lemma 4, statement details.** (a) "Every chamber contains a point (t, r)" should say "the image of a
point". (b) The final assertion silently uses q = 2^j together with the hypothesis q > (n+1) Delta_n / 2.
Suggested wording:

> Every chamber of the toric arrangement contains the image of a point (t, r) of P with ... Consequently,
> if moreover q = 2^j, every output-affine class ...

**4. Lemma 5, which columns.** The proof uses Cramer for every coordinate k = 0, ..., n, including the
constant column k = 0, and needs |Y_k| <= M_n for all k with the same Y. The definition of M_n should say
so. Suggested wording:

> Let M_n be the largest |det| of an (n+1) x (n+1) matrix whose rows have the form (1, x) with the entry
> in column k replaced by +-1, maximized over k in {0, 1, ..., n} (the same k for all rows; column 0 is
> the constant column) and over the signs. Every threshold function in n variables equals
> [Y_0 + Y.x > 0] for integers with |Y_k| <= M_n for every k = 0, ..., n simultaneously.

Remark (optional): for k >= 1 the row set is {(1, y, s)} up to a column permutation, so those matrices
give Delta_(n-1); the maximum M_n is attained at k = 0 for n >= 2 (computed below). The rest of the
proof is correct: the polyhedron is nonempty and pointed, the vertex is y = B^(-1) 1, Y = |det B| y is
integral (adjugate), s(x)(1, x).Y >= |det B| >= 1 gives realization with the strict sign, Y_k =
sign(det B) det(B_k), and multiplying row x of B_k by s(x) gives rows (1, x) with k-th entry s(x),
changing the determinant only by a sign. Whether rows with equal x are allowed in the definition does not
matter (the bound only needs to dominate matrices with distinct x; both versions give the same M_n).

**5. Section 2, the perturbation must not change T.** Suggested wording:

> If w_0 + w.x = 0 at some vertex, replace w_0 by w_0 - epsilon with 0 < epsilon smaller than every
> positive value of w_0 + w.x on the cube; this does not change T and makes w_0 + w.x nonzero at every
> vertex.

**6. Section 4, the folded threshold range: state the argument.** It is correct. Suggested wording:

> Folded range. Let T be a threshold function and Y as in Lemma 5. Complementing each input x_i with
> Y_i < 0 gives a threshold function realized by (Y_0 + sum over Y_i < 0 of Y_i, |Y_1|, ..., |Y_n|), and
> |Y_0 + sum over Y_i < 0 of Y_i| <= M_n + n M_n; permuting inputs then sorts the weights. So every
> threshold function lies in the hyperoctahedral orbit of one realized in
> 0 <= Y_1 <= ... <= Y_n <= M_n, |Y_0| <= (n+1) M_n, and closing the enumerated set under input
> permutations and complementations (which preserve threshold functions) gives exactly the threshold
> functions.

**7. Theorem 6 proof, two implicit steps.** (a) Passing from classes to function counts uses that BLF(n)
and the threshold XOR affine set are unions of cosets of the 2^(n+1) GF(2)-affine functions (Corollary
2), so tables = 2^(n+1) x classes. (b) For n = 5 the grid search was folded (gridfold.c). That is valid
because the grid of Lemma 4 is invariant under input permutations and complementations
((t, r) -> (t + r_i, ..., -r_i, ...) stays on Z/q), so a representative of each orbit of grid points
suffices, followed by closure. Suggested added sentence:

> BLF(n) and the threshold XOR affine functions are unions of cosets of the 2^(n+1) GF(2)-affine
> functions (Corollary 2), so each count of tables is 2^(n+1) times the count of classes; for n = 5 the
> grid points were taken up to input permutations and complementations, which map the grid of Lemma 4 to
> itself, and the classes found were closed under the same group.

**8. Minor, results file convention.** The 15 "minimal canonical tables" in results/runs_21nov.txt (and
0x7ee8 for n = 4) are valid representatives of the right orbits (checked: each lies in a distinct extra
orbit of the stated size), but they are not the minima under the obvious convention (bit x of the table
is f(x), x = x_1 + 2 x_2 + ..., minimize over affine XOR and then over the orbit); under that convention
the n = 4 class is 0x177e. Suggest stating the convention used in the results file. Not an issue in the
proof file itself.

Corollary 2, Proposition 3 and Section 5 are correct as written. (Corollary 2: complementing x_i gives
u'(x) = t + r_i + sum over k != i of r_k x_k - r_i x_i, affine; output complement is XOR with the affine
function 1. Section 5: reflection is an input permutation and complement conjugation is input
complementation plus XOR with 1, so classes are entirely in or out; ca_classes.py uses bit j of K + a.x
with 0 <= K, a_i < 2^(j+1) and j = 4, which by F1 gives whole cosets, and q = 16 > 12.)

## Computational checks (all reproduced)

Code: maxdet.c (Bareiss determinants), blfgrid.c (odd grid), thr.c (folded thresholds), analyze.py
(LP thresholds, NBC region count, closures, classes, orbits, CA), run5.py, gridcheck.py, repcheck.py.

**Delta_n (maxdet.c).** Different reduction from the project's: one row fixed to (1, 0, ..., 0, +1)
using the unimodular column operations x_i -> 1 - x_i and s -> -s, then all (n+1)-subsets of the other
rows. Result: Delta_0..Delta_5 = 2, 2, 4, 6, 10, 18 (n = 5 in 62 s). Matches the table.

**M_n (maxdet.c, full brute force, k = 0 and k = 1, with and without distinct x).**

| n | k = 0 | k >= 1 | M_n |
|---|---|---|---|
| 1 | 2 (1 if distinct x) | 2 | 2 |
| 2 | 3 | 2 | 3 |
| 3 | 5 | 4 | 5 |
| 4 | 9 | 6 | 9 |
| 5 | 18 | 10 | 18 |

Matches the table (k >= 1 equals Delta_(n-1) as remarked in Issue 4).

**Threshold counts, three methods.** (i) Number of regions of the central arrangement with normals
(1, x), computed as the number of no-broken-circuit sets (exact rank mod 2^31 - 1, which exceeds every
minor), no weights and no LP: 4, 14, 104, 1,882, 94,572 for n = 1..5. (ii) LP feasibility (HiGHS) for
all 2^(2^n) functions, n <= 4, each feasible solution verified exactly in rationals: 4, 14, 104, 1,882,
and the set equals (iii). (iii) My folded weight enumeration with my own M_n, closed under the
hyperoctahedral group: 4, 14, 104, 1,882, 94,572. Since (iii) produces only threshold functions and its
count equals the independent region count (i), the n = 5 list is complete.

**BLF classes, different grid.** u = (2K + 1)/(2q) + a.x/q with odd q (not a power of 2, half-odd t, so
every grid point is generic), folded to 0 <= a_1 <= ... <= a_n <= q/2, then closed. With
q = 3, 7, 13, 27, 55 (each just above (n+1) Delta_n / 2 = 2, 6, 12, 25, 54): BLF classes 1, 2, 13, 324,
29,747. Stable for other q: n = 3 gives 13 for q = 5 to 21; n = 4 gives 324 for q = 9 to 41; n = 5 gives
29,747 for q = 25 to 67. These equal (R_n + 1)/2 with R_n = 1, 3, 25, 647, 59,493 from PROOF_R116.md.

**Threshold XOR affine classes:** 1, 2, 13, 323, 25,997; every one lies in BLF. Extra classes: 0, 0, 0,
1, 3,750. Tables: BLF 4, 16, 208, 10,368, 1,903,808; threshold XOR affine 4, 16, 208, 10,336, 1,663,808;
extra functions 32 (n = 4) and 240,000 (n = 5).

**n = 4 extra class** equals the class of g(x) = bit 1 of x_1 + x_2 + x_3 + x_4 (exact set equality);
its hyperoctahedral orbit has size 1.

**n = 5 extra orbits:** 15 orbits, sizes (sorted) 1, 5, 32, 32, 80, 80, 160, 160, 160, 320, 320, 320, 480,
640, 960, the same multiset as stated (sum 3,750). The 15 tables listed in runs_21nov.txt fall into 15
distinct extra orbits with matching sizes. The class of bit 1 of x_1 + ... + x_5 is extra.

**Cellular automata:** |BLF(3)| = 208; 88 classes under reflection and complement conjugation; no mixed
class; 73 BLF and 15 not, minimal representatives 6, 9, 18, 27, 29, 33, 40, 46, 58, 72, 78, 130, 132,
172, 184; rule 110 is BLF.

Arithmetic in the table: 324 x 32 = 10,368; 323 x 32 = 10,336; 29,747 x 64 = 1,903,808;
25,997 x 64 = 1,663,808; 3,750 x 64 = 240,000; grid q = 4, 8, 16, 32, 64 all exceed (n+1) Delta_n / 2.

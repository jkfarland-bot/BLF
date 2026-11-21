# BLF functions: characterization, threshold XOR affine, and the small cases (R-096, R-107)

Rebuilt 21 Nov 2026 (Claude Opus 5.5, for team LKC01-T00316). Status: draft, needs an independent cold
reader. Notation as in PROOF_R116.md: for a real affine u(x) = t + r.x on {0,1}^n, F_u = floor(u) and
f_u = F_u mod 2; Lambda is the group of integer affine functions; BLF(n) is the set of maps
x -> bit j of (K + a.x) with j >= 0 and K, a_i integers (no bound on j; for negative N, bit j of N is
floor(N / 2^j) mod 2).

## 1. Characterization

**Proposition 1.** f is BLF iff f = f_u for some real affine u. (Proof: PROOF_R116.md, Proposition 1.)

**Corollary 2.** BLF(n) is closed under XOR with GF(2)-affine functions, under permutations of the
inputs, and under complementing any input.

Proof. XOR with m mod 2 is u -> u + m (m in Lambda). Permutation permutes the r_i. Complementing x_i
replaces u by t + r_i + sum_(k != i) r_k x_k - r_i x_i, again affine. []

## 2. Threshold XOR affine is always BLF

A threshold function is T(x) = [w_0 + w.x > 0] with real w; by a small perturbation (finitely many
strict inequalities) we may assume w_0 + w.x != 0 at every vertex.

**Proposition 3.** Every threshold function is BLF; hence (Corollary 2) every threshold function XOR a
GF(2)-affine function is BLF.

Proof. Let c = max over vertices of |w_0 + w.x| > 0 and put u = -(w_0 + w.x)/(2c). Then u(x) is in
[-1/2, 1/2] and nonzero at every vertex, so F_u(x) = -1 when T(x) = 1 and F_u(x) = 0 when T(x) = 0.
Thus f_u = T. []

## 3. Two finite reductions (both proved, then checked by exhaustive computation)

**Lemma 4 (universal grid for BLF).** Let Delta_n be the largest |det| of an (n+2) x (n+2) matrix whose
rows are taken from {(1, x, s) : x in {0,1}^n, s = +-1}, and let q > (n+1) Delta_n / 2. Every chamber of
the toric arrangement contains a point (t, r) with r in (Z/q)^n and t in Z/q, and also one with r in
(Z/q)^n and t in (2Z + 1)/(2q). Consequently, when q = 2^j, every output-affine class of BLF(n) is the
class of x -> bit j of K + a.x for some integers 0 <= K, a_i < q.

Proof. A chamber lifts to a region P = {(t, r) : F(x) < t + r.x < F(x) + 1 for all x}, nonempty, open and
bounded (t and each t + r_i lie in unit intervals). Maximize delta subject to t + r.x - delta >= F(x),
t + r.x + delta <= F(x) + 1 (all x), delta <= 1. The feasible set is a nonempty polytope and the optimum
delta* is positive because P is open. If the cap is not tight at an optimal vertex, that vertex solves
n + 2 tight constraints with rows (1, x, -+1) and integer right-hand sides, so by Cramer delta* = N / det
with N a nonzero integer and |det| <= Delta_n, giving delta* >= 1/Delta_n; otherwise delta* = 1. Let
(t, r) be an optimal point and round t to the nearest point of Z/q (or of (2Z + 1)/(2q)) and each r_i to
the nearest point of Z/q. Each coordinate moves by at most 1/(2q), so each t + r.x moves by at most
(n+1)/(2q) < 1/Delta_n <= delta*: the rounded point is still in P. For the last assertion, every BLF
class is the class of a chamber (PROOF_R116.md, Proposition 1 and F3), and at the point (K, a)/q of that
chamber f_u is bit j of K + a.x; reducing K and each a_i mod q changes it by a GF(2)-affine function
(PROOF_R116.md, F1). []

**Lemma 5 (weight bound for thresholds).** Let M_n be the largest |det| of an (n+1) x (n+1) matrix whose
rows are (1, x) with the entry in one fixed column k (the same k for all rows) replaced by +-1. Every
threshold function in n variables equals [Y_0 + Y.x > 0] for integers with |Y_k| <= M_n.

Proof. Write s(x) = +1 if T(x) = 1 and -1 otherwise. The polyhedron {y in R^(n+1) : s(x) (1, x).y >= 1
for all x} is nonempty (scale a strict realization) and pointed (the vectors (1, x) span R^(n+1)), so it
has a vertex y, the solution of B y = 1 for n + 1 linearly independent tight rows s(x)(1, x). The integer
vector Y = |det B| y satisfies s(x)(1, x).Y >= |det B| >= 1, so it realizes T. By Cramer, Y_k is +- the
determinant of B with column k replaced by the all-ones vector; multiplying each row by its s(x) turns
that matrix into one with rows (1, x) whose k-th entry is s(x), so |Y_k| <= M_n. []

## 4. Computed values (exhaustive, exact integer arithmetic; code in compute/)

| n | Delta_n | grid q used | M_n | thresholds | thr XOR aff classes | BLF classes | extra classes (orbits) | BLF tables |
|---|---|---|---|---|---|---|---|---|
| 1 | 2 | 4 | 2 | 4 | 1 | 1 | 0 | 4 |
| 2 | 4 | 8 | 3 | 14 | 2 | 2 | 0 | 16 |
| 3 | 6 | 16 | 5 | 104 | 13 | 13 | 0 | 208 |
| 4 | 10 | 32 | 9 | 1,882 | 323 | 324 | 1 (1) | 10,368 |
| 5 | 18 | 64 | 18 | 94,572 | 25,997 | 29,747 | 3,750 (15) | 1,903,808 |

Threshold enumeration (thresh.c): all |Y_k| <= M_n directly for n <= 4, and for n = 5 the folded range
0 <= Y_1 <= ... <= Y_n <= M_n, |Y_0| <= (n+1) M_n (complementing inputs changes Y_0 by at most n M_n)
closed under input permutations and complementations; the folded and direct enumerations agree for
n <= 4. The threshold counts are the known values (OEIS A000609). Every threshold XOR affine class lies
in BLF (0 outside, as Proposition 3 requires).

The n = 5 extra orbits have 5, 80, 80, 320, 320, 480, 960, 160, 640, 160, 1, 32, 160, 320, 32 classes
(sum 3,750; minimal canonical tables in results/runs_21nov.txt).

**Theorem 6 (R-096).** (a) For n <= 3, BLF(n) is exactly the set of threshold functions XOR GF(2)-affine
functions: 4, 16, 208 functions for n = 1, 2, 3.
(b) |BLF(4)| = 10,368 = 10,336 (threshold XOR affine; 1,882 thresholds) + 32, and the 32 extra
functions are the affine translates of g(x) = bit 1 of x_1 + x_2 + x_3 + x_4.
(c) |BLF(5)| = 1,903,808 = 1,663,808 threshold XOR affine + 240,000 in 3,750 extra classes, 15 orbits
under the hyperoctahedral group.

Proof. Lemma 4 (with the computed Delta_n) makes the grid search complete, Lemma 5 (with the computed
M_n) makes the threshold search complete, and Proposition 3 gives the inclusion; the table records the
exhaustive results. []

## 5. Elementary cellular automata (3 inputs l, c, r)

Rule R has f(l, c, r) = bit 4l + 2c + r of R. BLF(3) is closed under the CA symmetries (reflection
permutes inputs; conjugation by complement complements every input and the output), so each of the 88
classes is entirely in or entirely out of BLF (checked: no mixed class). Of the 88 classes, 73 are BLF
and 15 are not: 6, 9, 18, 27, 29, 33, 40, 46, 58, 72, 78, 130, 132, 172, 184 (ca_classes.py, brute force
of bit j of K + a.x with j <= 4). Rule 110 is BLF.

## 6. Provenance

Statements: seat BL-O (Claude, 5 Nov) for the characterization, n <= 3 and the CA classes; n = 4 count
and decomposition first computed by ChatGPT (OpenAI) answer A2; n = 5 count and structure by ChatGPT
answers to Q13 (checked by the director, 9 Nov). This file: new proofs of Lemmas 4 and 5 and new code;
every number above recomputed 21 Nov.

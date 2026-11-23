# Cold read of Q22 (toric lower bound log2 R_n >= n^2 - (1/2) n log2 n - O(n))

## Verdict

PROVED WITH MINOR REPAIRS. The lower bound holds unconditionally from KKS Corollary 4(b).
I found no mathematical gap. The repairs are wording and citation fixes: (i) say why the
KKS event is exactly "not good" when Z is nonzero, (ii) cite the Möbius sign theorem for
the vertex contributions and note that the slice normals span, (iii) the phrase "dependence
estimate" in the KKS paragraph is unneeded and should go. None of these changes a constant.
All constants are absolute once k = C (the KKS constant) is fixed; the loss is -(k-1)n + O(log n).

## KKS Corollary 4(b): what it says and whether it applies

- KKS (JAMS 8 (1995), p. 238, Corollary 4): there is an absolute C such that if r <= n - C and
  v_1..v_r are independent uniform in {+-1}^n, then (a) a dependence statement and (b) the
  probability that span{v_i} meets {+-1}^n in more than {+-v_1..+-v_r} is
  (1+o(1)) 4 binom(r,3) (3/4)^n. The scanned text I could read garbles the formula and the
  displayed set; the OCR shows "{v_1..v_r}" without +-. Read literally that event has
  probability 1, so the +- reading is the only sensible one. The proof notes this; agreed.
- Ferber, Jain, Zhao restate it cleanly (CPC 31 (2022), Theorem 1.6; arXiv 1808.07222,
  Theorem 1.7): r <= n - C implies P[d_pm(span) > log2(2r)] = (1+o(1)) 4 binom(r,3)(3/4)^n,
  where 2^{d_pm(W)} = |W cap {+-1}^n|. So the event is |span cap {+-1}^n| > 2r.
- Applies here exactly. Dimension d = n+1, r = d - k with k >= C fixed, so r <= d - C.
  Sign rows s, normalized to s_0 = +1, then x_i = (1 - s_i)/2, give v = (1,x) = s T with T
  invertible (det T = (-1/2)^n). So v_y in span(V_B) iff s_y in span(S_B). A +-1 vector w in
  span(S_B) can be scaled by w_0 to first coordinate +1. Hence "B good" iff span(S_B) has no
  +-1 vector except +-rows of S_B. Row sign flips do not change Z or the event, so normalized
  and unnormalized laws agree.
- Repair (i): KKS's event is |W cap {+-1}^d| > 2r. This equals "not good" only when the
  2r vectors +-v_i are distinct. That holds whenever Z != 0 (rows independent). Since the
  proof only uses Z 1_{not good} <= Z 1_{E_KKS}, this is enough. Say so explicitly.
- The bound is asymptotic (1+o(1)). It gives P(bad) <= 8 binom(r,3)(3/4)^d for n >= n_0.
  With r = d - k this is one sequence, so uniformity in r is not an issue.

## Step-by-step check

1. (1) R_n = sum_S (-1)^{|S|-d} g(S) <= D_n. OK. Regions = (-1)^d chi(0) = sum over vertices
   v of |mu(0,v)| (Ehrenborg, Readdy, Slone, Thm 3.5; hypothesis: regions are open balls,
   true because normals span, so lifted cells are bounded convex and project injectively).
   |mu(0,v)| = number of NBC bases at v <= number of bases at v; summing gives D_n.
   Verified numerically for n <= 4 (below).
2. (2) det(V^T V) = m^d/4^n and D_n <= m^d/(2^n sqrt(d!)). OK (Cauchy-Binet, binom(m,d) <= m^d/d!).
3. Slice: freeze the last k cube coordinates z_{r..n} at t. Slice normals a_x = (1, x_1..x_{r-1})
   have first entry 1 (primitive) and span R^r. OK.
4. At most 2^k slice components per full chamber. OK. Walls x=0 and x=e_i bound z_0 and
   z_0+z_i to open unit intervals on a lift P, so z_i lies in an open interval of length 2;
   at most 2 integer shifts per frozen coordinate meet P; each piece is convex; P projects
   injectively (a bounded cell cannot meet its own nonzero translate).
5. Slice regions are exactly the slice pieces of full chambers. OK: S minus walls =
   disjoint union of S cap C, each open in S. So R_slice <= 2^k R_n.
6. Good B gives simple vertices. OK. The elimination gives (b_y - a_y A^-1 W) t in Q; a zero
   coefficient vector puts v_y in the full span of B. Distinct good B give disjoint vertex
   sets (a shared vertex would carry the other basis's walls, so it is not simple).
7. Regions >= simple vertices. OK with repair (ii). Use ERS Thm 3.5 on the slice (normals
   span, item 3), then sign alternation: [0,v] is the intersection lattice of the local
   central arrangement, a geometric lattice, so (-1)^r mu(0,v) >= 1 (Rota). Non-simple
   vertices contribute at least 1, not just >= 0. Simple vertices contribute exactly 1.
   ERS Thm 3.5 needs no genericity, so it covers the rational slice too.
8. Rational certificate t_j = L^-j, H = (r+1)^(r+1), L = H+2. OK. Multiply the vertex
   condition by Delta = det A_B: sum_j c_j t_j must be an integer, with c_j the bordered
   (r+1)x(r+1) 0/1 determinant (Schur complement), |c_j| <= (r+1)^((r+1)/2) <= H. If c != 0,
   the leading term beats the tail (H/(L-1) < 1) and |sum| < 1, so it is a nonzero non-integer.
   Note: these t are rational, so "rationally independent" in the text should read "or this
   explicit rational choice"; the certificate replaces independence. Fine.
9. |det A| = Z/2^(r-1). OK. A uses only the first r columns of V, which are s_0 and
   (s_0 - s_i)/2 for i < r; determinant factor (-1/2)^(r-1).
10. E Z^2 = r!. OK. E Z^4 <= r!(r+2)!/2. OK: Gaussian swap adds 2a^4 >= 0 per entry; Gaussian
   |det|^2 is a product of independent chi^2_j, E(chi^2_j)^2 = j(j+2). Hölder:
   E Z >= (EZ^2)^(3/2)/(EZ^4)^(1/2) = sqrt(r!) sqrt(2/((r+1)(r+2))). OK.
11. Cauchy-Schwarz: E[Z 1_bad] <= sqrt(E Z^2 P(bad)) = sqrt(r!) O(rho^(d/2)). No independence
   is needed. Versus sqrt(r!)/O(n), so E[Z 1_good] >= half the Hölder bound for n >= n_0. OK.
12. Ordered to unordered: sum_B good |det A_B| = (m^r/r!) E[|det A| 1_good]; tuples with a
   repeat have two equal rows, det 0. OK.
13. (5): 2^-k * 2^-(r-1) * (1/2) = 2^-d. OK. log2 of (5) = n(n+1-k) - (n+1) - (1/2)log2 r! - O(log n)
   = n^2 - (1/2) n log2 n - O(n), with the O(n) depending only on k = C. Small n (< n_0) are
   absorbed in O(n) since log2 R_n >= 0. OK.
14. Repair (iii): the sentence "Their logarithmic cube-intersection-size formulation,
   together with the dependence estimate, gives the required exponentially small bad event"
   should be replaced by the one line in repair (i). No dependence estimate is used.

## What I computed (exact integer/Fraction arithmetic, scripts in scripts/)

- Full arrangement, n = 1..4, by vertex Möbius sum: R = 1, 3, 25, 647 (matches team values).
  Independent Monte Carlo floor-vector count (200k points): 1, 3, 25, 647.
- Formula (1) by direct inclusion-exclusion over all wall subsets, n = 1..4: 1, 3, 25, 647.
- D_n = 1, 4, 60, 3360 (n = 1..4); sum det^2 = m^d/4^n exactly; D_n <= bound (2): 1.4, 6.5, 104.5, 5982.6.
- Slice inequality chain sum_good|det A_B| <= #simple vertices <= R_slice <= 2^k R_n, with the
  proof's own t_j = L^-j (and a second generic rational t, same counts):
  n=2,k=1: 4 <= 4 <= 4 <= 6.  n=3,k=1: 8 <= 8 <= 26 <= 50.  n=3,k=2: 16,16,16 <= 100.
  n=4,k=1: 96 <= 112 <= 520 <= 1294.  n=4,k=2: 112,112 <= 220 <= 2588.  n=4,k=3: 64,64,64 <= 5176.
  n=5,k=2: 3072 <= 3200 <= 9856 <= 237972.  n=5,k=3: 1184,1184 <= 1832 <= 475944.
  n=5,k=4: 256,256,256 <= 951888.  n=5,k=1: 3456 <= 3776 <= 34518 <= 118986.
  All chains hold; (3) holds in every case.
  Monte Carlo cross-check of R_slice (generic t): equal, except n=4,k=1 gives 504 < 520
  (thin regions missed by sampling, as expected for a lower count).
- Moments of Z, r = 1..5 (exhaustive, column 0 fixed to +1): E Z^2 = r! exactly;
  E Z^4 = 1, 8, 96, 2112, 68160 vs bound 3, 24, 360, 8640, 302400; E Z = 1, 1, 1.5, 2.8125,
  6.1523 vs Hölder bound 0.577, 0.577, 0.775, 1.265, 2.390. All hold.
- Monte Carlo of the KKS event with k = 3, d = 8..16: P(bad) is near 1 and the KKS main
  term 4 binom(r,3)(3/4)^d is 4 to 12. So at these sizes almost no r-set is good.

## Caveats

- The bound is purely asymptotic. KKS gives no explicit C or n_0, and the main term
  4 binom(r,3)(3/4)^d with r = d - k only drops below 1/2 near d = 50 to 60. Nothing here
  gives a usable explicit constant in O(n), and (5) should not be read as valid for small n
  (it is not needed there; e.g. n = 4, k = 1 gives the much weaker 48 <= 647).
- I could not read KKS Corollary 4(b) cleanly in the original scan (formula garbled in OCR).
  The statement above rests on FJZ's restatement plus the readable parts of the scan
  (r <= n - C, uniform independent vectors, "span no other +-1 vectors", improves Odlyzko).
- The O(n) gap between (2) and (5) is real; the proof correctly claims no linear coefficient.
- I did not check the BLF identity |BLF(n)| = 2^n(R_n+1) or the Xie preprint remark; not used.
- Full R_5 was not recomputed (team value used only in the slice chain upper end).

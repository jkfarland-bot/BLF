# Cold read of PROOF_R116 (|BLF(n)| = 2^n (R_n + 1))

Reader: independent cold reader, 21 Nov 2026. Source read: /home/claude/blf/proofs/PROOF_R116.md (not modified).
Code written from scratch in /home/claude/coldread_R116/ (grid_count.py, lemma3_check.py, blf_direct.py).

## Verdict

**Proved, with minor repairs (presentation only).** Every step was checked line by line and I found no
mathematical error, sign error, off by one, or unjustified genericity. Lemma 3 is correct as written,
including the rigid case. The issues below are places where a one line justification is missing or
notation is overloaded; none of them changes the argument.

## Line by line notes on the key steps

- (F1), (F2), (F3), Proposition 1: correct. F3 needs e smaller than the distance from each non integer
  u(x) up to the next integer; this is implicit in "small".
- Lemma 2: correct. The P_F are open, convex, pairwise disjoint and cover the generic points, so they
  are the components. Injectivity on a region: u and u + m in the same P_F forces m = 0 on the cube,
  hence m = 0. See issue 1 for the one missing sentence (surjectivity of a region onto its chamber).
- Lemma 3, carries: F(x + e_i) = F(x) + k_i + floor(a(x) + alpha_i), and a + alpha_i lies in (0, 2), so
  the carry is [a + alpha_i >= 1]. Correct.
- Types: k_i + A_i = m_i + C_i (mod 2) with A_i, C_i in {0, 1} gives A_i = C_i everywhere or
  A_i = 1 - C_i everywhere, according to the parity of m_i - k_i. Exactly one type. Correct.
- Step 1: path i then j for u gives k_i + kappa + k_j + lambda', path j then i gives
  k_j + lambda + k_i + kappa'. For w the same with C. Subtracting the m, k constants and adding the two
  relations gives 2 kappa = 2 kappa'. Correct. Flipping x_j (j of type D) keeps x_i = 0, so the
  comparison is between two genuine i-edges.
- Step 2: increments recomputed: type S edge, g changes by alpha_i + beta_i - 2A_i, h by alpha_i - beta_i;
  type D edge, c changes by beta_j - 1 + A_j, so g changes by alpha_j + beta_j - 1 and h by
  alpha_j - beta_j + 1 - 2A_j. Matches the text. The path argument gives
  g(x) = g(x_S, 0) + sum_{j in D} (alpha_j + beta_j - 1) x_j and h(x) = h(0, x_D) + sum_{i in S} (alpha_i - beta_i) x_i.
  (*) holds since |g| + |h| = max(|2a - 1|, |2c - 1|) < 1.
- Step 3: second difference of g over an (i, k) face equals the difference of the two i-increments,
  -2(A_i(x + e_k) - A_i(x)). Triangle inequality gives sum |g| >= 2 on each of the 4 copies of Q_S,
  so >= 8 on the 16 vertices; (*) and sum |h| >= 2 on each copy of Q_D give sum |g| < 2 there, so < 8.
  Contradiction is valid. Non rigidity of i in I_S forces |I_S| >= 2 (if I_S = {i} then A_i depends on
  no free coordinate), so k exists. Same for D.
- Step 4: with A_j constant on every type D direction, the D-increment (k_j - m_j - 1)/2 + A_j is
  constant; type S increments of D are (k_i - m_i)/2. So D(x) = D(0) + sum delta_i x_i with integer
  delta_i, D in Lambda, G = F - 2D. Other case: S in Lambda and floor(-w) = -G - 1 = F - 2S - 1. Both
  correct; the "or" in Step 3 covers the cases I_S or I_D empty.
- Lemma 4: -C = C gives -P = P + m, so P is invariant under y -> -y - m and contains -m/2 by
  convexity. Half integer generic points: x = 0 forces m_0 odd, x = e_i then forces m_i even. Unique
  point (1/2, 0, ..., 0) mod Z^(n+1). Correct.
- Theorem 5: correct. Each class has exactly 2^(n+1) elements (the GF(2)-affine functions in n variables
  are 2^(n+1) distinct functions), and Lemma 4 makes R_n odd.

## Issues and suggested wording

1. **Lemma 2, chamber versus orbit (missing sentence).** The text says the projection maps each
   Lambda-orbit of regions "onto one chamber" but does not say why the image of a region is the whole
   chamber and why different orbits give different chambers. Suggested addition after "...injectively
   on each region.": "The preimage in R^(n+1) of the complement of the toric arrangement is the set of
   generic points, and the projection is a covering map. The image of a region P is open and connected;
   its preimage is the union of the translates P + m, which is closed in the generic set (its complement
   there is a union of other regions), so the image is also closed in the complement on the torus and is
   therefore a whole chamber. Two regions with the same image intersect after a translation, hence lie in
   one Lambda-orbit."

2. **Notation clash m.** In Lemma 3, m denotes the lift in Lambda ("replace w by w + m") and m_i denotes
   the integer part of w_i. Suggested fix: "By (F1) replace w by w + mu (mu in Lambda lifting the affine
   difference)" and keep m_i, or rename the integer parts to l_i.

3. **Lemma 3, restatement for the original w.** Step 4 concludes for the shifted w. Add at the end of
   Step 4: "Since the shift w -> w + mu in the first line does not change the chamber of w, the same
   conclusion holds for the original w."

4. **Step 3, existence of k and of the face.** Suggested wording: "Since A_i depends on x_S only and
   x_i = 0 on i-edges, A_i is a function on the cube {0,1}^(I_S minus {i}). It is not constant, and a
   non constant function on a cube changes along some edge; this gives k in I_S, k != i, and a point x
   with A_i(x) != A_i(x + e_k). Let Q_S be the 2-face of {0,1}^(I_S) spanned by e_i, e_k at x_S. Because
   A_i does not depend on x_D, the second difference of g over Q_S x {x_D} is the same +-2 for every x_D."

5. **Step 2, derivation of (*).** Add: "Indeed |g| + |h| = max(|g + h|, |g - h|) = max(|2a - 1|, |2c - 1|)."

6. **Step 4, constancy of the D-steps in rigid directions.** Make explicit: "For j in I_D,
   D(x + e_j) - D(x) = (k_j - m_j - 1)/2 + A_j(x), which is constant when j is rigid."

7. **Proposition 1, definition of BLF (hidden assumption).** The count depends on BLF(n) allowing every
   bit index j >= 0 and all nonnegative integers K, a_i, with no bound on the bit width. State it:
   "Here BLF(n) is the set of maps x -> bit j of (K + a.x) with j >= 0 and K, a_1, ..., a_n nonnegative
   integers, no bound on j. For negative N, bit j of N means floor(N / 2^j) mod 2." If the ledger bounds
   j or the word size, the identity needs that bound to be large enough (my direct enumeration reaches
   the full set already at j <= 2 for n = 3 and j <= 3 for n = 4).

8. **Lemma 4, negation on chambers.** Add: "The arrangement is invariant under p -> -p, so negation maps
   chambers to chambers, and -P is a region lifting -C." Also state that Lemma 4 implies R_n is odd,
   which Theorem 5 uses when writing (R_n - 1)/2.

9. **Section 5.** The grid counts are lower bounds unless the grid is proved universal; the text relies
   on the maxminor bound for that. My own grid (different construction, see below) independently gives
   the same R_1..R_5, which supports the stated values but is not a proof of them. Suggested wording:
   "R_n values are confirmed by two independent methods (universal grid and no-broken-circuit formula)."

## Computational checks (all exact; written from scratch)

**A. Chamber and class counts (grid_count.py).** Points u(x) = (T + 1/2 + R.x)/q, all generic, F computed
in integers. Chambers keyed by F minus the integer affine interpolant at 0 and e_i; classes keyed by f
XOR its GF(2)-affine interpolant. For each class I checked the chambers hitting it: at most 2, and if 2,
they are antipodal ("bad_classes").

| n | q | chambers | classes | (R+1)/2 | self antipodal | bad classes | 2^(n+1) x classes |
|---|---|---|---|---|---|---|---|
| 1 | 4, 8 | 1 | 1 | 1 | 1 | 0 | 4 |
| 2 | 4, 8, 16 | 3 | 2 | 2 | 1 | 0 | 16 |
| 3 | 8, 16, 24 | 25 | 13 | 13 | 1 | 0 | 208 |
| 4 | 8, 16 | 647 | 324 | 324 | 1 | 0 | 10368 |
| 5 | 8 | 44133 (incomplete grid) | 22067 | 22067 | 1 | 0 | |
| 5 | 12, 16 | 59493 | 29747 | 29747 | 1 | 0 | 1903808 |

The chamber set was closed under antipode in every run. The values agree with R_1..R_5 in Section 5.

**B. Direct enumeration of BLF(n) (blf_direct.py),** bit j of K + a.x with 0 <= K, a_i < 2^(j+1):
|BLF(2)| = 16 (stable for j <= 4), |BLF(3)| = 208 (stable from j = 2 to 5), |BLF(4)| = 10368 (stable at
j = 3, 4). These equal 2^n (R_n + 1) for n = 2, 3, 4.

**C. Lemma 3 and its intermediate claims (lemma3_check.py, Python Fractions, seed 1).** For each pair
(u, w) of generic rational points with f_u XOR f_w affine, the script lifts the difference, then checks:
carry and step formulas for F, G, a, c; every direction has exactly one type and it matches the parity of
m_i - k_i; Step 1 invariance on every mixed face; the decompositions g = g(x_S, 0) + L_D and
h = h(0, x_D) + L_S with the stated linear coefficients; (*); the Step 3 dichotomy (all S rigid or all D
rigid); the Step 4 conclusion (D or S integer affine, chamber equal or antipodal accordingly); and
directly that the chamber of w is that of u or of -u.

- Experiment A (independent random generic pairs, denominators from {7, ..., 1009}): pairs with
  affine XOR found and checked: n = 2: 2344, n = 3: 835, n = 4: 196, n = 5: 52, n = 6: 11.
- Experiment B (many small denominator samples grouped by class, every pair of distinct chambers in a
  class checked both ways): n = 2 q = 8: 158 pairs; n = 3 q = 12: 290; n = 4 q = 16: 1588 (324 classes,
  646 chambers seen); n = 5 q = 6: 1988; n = 5 q = 10: 3382; n = 6 q = 4: 1095; n = 6 q = 6: 2760. No class
  was ever hit by more than 2 chambers.
- Experiment C (adversarial hill climb: w starts outside the chambers of u and -u and moves by random
  rational steps to minimise the Hamming distance from f_u XOR f_w to the affine functions; each time the
  distance reaches 0 the full check runs): successes n = 2: 119, n = 3: 245, n = 4: 185, n = 5: 137,
  n = 6: 71. Every success landed in the chamber of u or of -u.
- Totals over A, B, C of fully checked pairs: n = 2: 2621, n = 3: 1370, n = 4: 1969, n = 5: 5559,
  n = 6: 3937. Of these, pairs with both types present: 1093, 752, 694, 3234, 2493. Pairs with a non rigid
  type S direction and some type D direction: 0 (n = 2), 61, 206, 388, 112; with a non rigid type D
  direction and some type S direction: 0, 52, 76, 1817, 1787, so both branches of Step 4 and the rigid
  handling were exercised. Chamber of w equal to that of u: 2424, 1174, 1251, 2824, 1936; antipodal:
  197, 196, 718, 2735, 2001.
- Failures of any check: 0.

## Summary

The argument is complete for every n >= 1 (and trivially n = 0). Lemma 3 is the substantive step and is
correct: the type split, the mixed face invariance, the g/h decomposition, and the 16-vertex
contradiction all check out, and genericity enters only through a, c in (0, 1), which is exactly what (*)
needs. The repairs are wording additions (issues 1 to 9), the most important being the explicit
definition of BLF(n) (issue 7) and the covering-map sentence in Lemma 2 (issue 1).

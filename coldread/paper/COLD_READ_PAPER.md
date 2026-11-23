# Cold read of the BLF preprint (blf.tex, version 1, 23 Nov 2026)

Reader: independent cold reader (did not write the paper). Source: /home/claude/paper_blf/blf.tex (not
modified). Own code: /home/claude/coldread_paper/code/. Repository checked: /home/claude/blf.

## Overall verdict

No mathematical gap. Every result is proved, or correctly certified, as stated, after the repairs
below. The new material (the proof of Theorem 7.1 with both bounds, Corollary 7.3, Proposition 8.1,
the proof outline of Theorem 5.1 and the text of Section 6) is correct. There is one real numerical
error: the list of linear coefficients in the Status line of Theorem 7.1 is for log2 |BLF(n)|, not
for log2 R_n (Issue 1). There are also two places where the paper says more than it has shown: the
Status line of Theorem 7.1 says an earlier cold read covers the rebuilt proof text (Issue 2), and
Section 8 treats an Announced result as known (Issue 8). Proposition 8.1 needs one missing sentence
(Issue 7). Everything else is wording or citation precision.

## Verdict per result

- Prop 2.1 (characterization): **Proved**. Dyadic points are dense in the open set; the nonnegativity reduction is correct.
- Prop 2.2 (closure): **Proved**. Status accurate (Lean: `BLF.isBLF_xor_affB`, XOR part only).
- Prop 2.3 (thresholds): **Proved**. Status needs a clarification on integer weights (Issue 13).
- Lemma 2.4 (parallelogram): **Proved**. Lean name and meaning checked.
- Lemma 3.1 (chambers): **Proved**.
- Lemma 3.2 (core lemma): **Proved**. Rechecked Steps 1 to 4, including (2) via |p+q|+|p-q| = 2 max(|p|,|q|) and the step formulas for S and D.
- Lemma 3.3 (antipode): **Proved**.
- Thm 3.4 (toric identity): **Proved**. Status matches coldread/R116 (9 issues; 2621+1370+1969+5559+3937 = 15456 pairs).
- Lemma 4.1 (universal grid): **Proved**. Minor notation (Issue 17). C(32,6) = 906192 and C(64,7) = 621216192 subsets checked.
- Lemma 4.2 (threshold weights): **Proved**.
- Thm 5.1 (small n), proof outline: **Proved (Lean); outline correct**. Checked |G(x)| <= |x| - 1 by induction, the canonical form, and the 1,1,0,0 obstruction (it matches BLF/Strict.lean). Variable clash (Issue 14).
- Thm 5.2 (n = 5): **Correct (Computer)**. All numbers reproduced with my own code (below).
- Cor 5.3 (CA): **Correct (Computer)**. Reproduced. The proof cites the wrong item (Issue 11).
- Thm 6.1 (counts): **Correct (Computer)**. Table arithmetic checked; n <= 5 reproduced by me; n = 6 from runs_21nov.txt only (Issue 10).
- Prop 6.2: **Correct as a computer statement**. The logic (one inclusion plus equal counts) is sound.
- Thm 7.1, upper bound: **Proved**. Gram determinant, Cauchy-Binet, Cauchy-Schwarz and R_n <= D_n all checked.
- Thm 7.1, lower bound: **Proved with repairs**. See the detailed check. Repairs: Issues 3, 4, 5, 21 (wording and citation only).
- Thm 7.2 (KKS): **Correctly quoted**. Agrees with FJZ (arXiv numbering Theorem 1.7; Issue 6).
- Cor 7.3: **Proved**. Cover's bound needs one phrase for points not in general position (Issue 16). Finite shares checked.
- Prop 8.1: **Proved with repair**. Classes vs functions at a fixed bit (Issue 7). Hadamard bound and counting bound checked.
- Announced 9.1, 9.2: **Not assessed (not claimed)**. The framing is correct, but Section 8 uses 9.1 as if known (Issue 8).

## Detailed check of Theorem 7.1

Upper bound. |mu(p, 1^)| = #NBC bases <= #bases of the local arrangement at p. Summing over p gives
D_n = sum_B |det V_B|, because a basis has walls through exactly |det V_B| torus points (the group
V_B^{-1} Z^d / Z^d). For the Gram matrix V^T V: subtracting half of row 0 from row i gives
row 0 = (m, m/2, ..., m/2) and row i = (m/4) e_i, which is upper triangular, so det = m^{n+1}/4^n.
Cauchy-Schwarz over all C(m,d) row sets (singular ones included) with Cauchy-Binet, and
C(m,d) <= m^d/d!, gives m^d/(2^n sqrt(d!)). The logarithm is n(n+1) - n - (1/2) log2 (n+1)!. Correct.
I recomputed D_n and sum det^2 = m^d/4^n exactly for n <= 4.

Lower bound, step by step.
- Slice. The frozen indices j = r..n are k = d - r coordinates, and the slice is T^r with normals
  a_x = (1, x_1..x_{r-1}) that span R^r. Correct.
- (a) On a lift P, z_j = (z_0 + z_j) - z_0 lies in an open interval of length 2, which contains at
  most two points of t_j + Z. Each choice of integer shifts gives a convex (hence connected) piece.
  The projection is injective on P. The slice minus its walls is the disjoint union of the open sets
  Sigma meet C. So each chamber gives at most 2^k slice regions and R_Sigma <= 2^k R_n. Correct, but
  the word "translates" is loose (Issue 4).
- (b) ERS covers rational normals with real constants, so the vertex formula applies to the shifted
  slice once the regions are open cells, which holds because the normals span (Issue 5). Rota: [p, top]
  is the intersection lattice of the essential local central arrangement, so |mu| >= 1. A simple
  vertex gives a Boolean lattice, so |mu| = 1. Correct.
- (c) Delta(a_y z' + c_y) is an integer, and Delta lambda . N is an integer, so Delta(c_y - lambda c_B)
  is an integer. gamma_j = Delta y_j - (Delta lambda).(x_j) equals the bordered (r+1) x (r+1) 0/1
  determinant exactly (Schur complement). By Hadamard |gamma_j| <= (r+1)^((r+1)/2) <= H. If all
  gamma_j = 0, then v_y = sum lambda_x v_x, which goodness excludes. Otherwise the leading term gives
  |sum| >= L^{-j0}(1 - H/(L-1)) > 0, because H/(L-1) = H/(H+1) < 1. The tail gives
  |sum| <= H L^{1-r}/(L-1) < 1 for r >= 1. Correct. The disjointness of vertex sets for distinct good
  sets is also correct. This applies too when a_y = a_x for some x in B: then the walls are parallel
  and distinct, because their c's differ by a nonzero non-integer.
- (d) The ordered-to-unordered factor m^r/r! is right, since repeats give det 0. A = S T with
  T = [[1, 1/2, ..., 1/2], [0, -1/2, ...], ...] upper triangular, so det T = (-1/2)^{r-1}. The law of
  Z is right. E Z^2 = r!. The Gaussian swap adds 2 E alpha^4 (odd moments vanish; E g^4 - E eps^4 = 2).
  Bartlett gives prod j(j+2) = r!(r+2)!/2. Hoelder: E Z^2 <= (E Z)^{2/3}(E Z^4)^{1/3}, which gives
  sqrt(r!) sqrt(2/((r+1)(r+2))). Correct.
- KKS event. (1,x) -> (1,1-2x) is the linear map (v_0, v) -> (v_0, v_0 - 2v). Bad iff the span
  contains a sign vector other than +-s~(i) (normalize by the first coordinate). Z != 0 means the
  s~(i) are independent, so the 2r vectors +-s~(i) are distinct, and {Z != 0, bad} lies in
  {|span meet {+-1}^d| > 2r}. Normalizing first coordinates does not change spans or the law.
  Correct. Cauchy-Schwarz on Z 1_{bad, Z != 0} is correct. The step from "E[Z 1_bad] < half the
  Hoelder bound" to "E[Z 1_good] >= E Z / 2" is valid, because the Hoelder bound is <= E Z, but it
  is not said (Issue 21).
- Arithmetic. 2^{-k} 2^{-(r-1)} 2^{-1} = 2^{-(k+r)} = 2^{-d}. The display is correct. The logarithm
  is n(n+1-k) - (n+1) - (1/2) log2 r! - O(log n) = n^2 - (1/2) n log2 n - O(n), with the constant
  depending on k only. Small n are absorbed because log2 R_n >= 0. Correct.

## Numbered issues with suggested replacements

1. (Error, Thm 7.1 Status) The listed values 1.000, 0.500, 0.359, 0.335, 0.333, 0.349 are
   (log2 |BLF(n)| - n^2 + (1/2) n log2 n)/n. For log2 R_n the same ratio is -1.000, -0.708, -0.660,
   -0.666, -0.667, -0.651. Replace "The linear term of $\log_2 R_n$ is open: $\log_2 R_n - n^2 +
   \frac12 n\log_2 n$ divided by $n$ is $1.000, 0.500, 0.359, 0.335, 0.333, 0.349$ for $n = 1, \dots,
   6$." with:
   `The linear term is open: $(\log_2 |\BLF(n)| - n^2 + \frac12 n\log_2 n)/n$ is $1.000, 0.500, 0.359, 0.335, 0.333, 0.349$ for $n = 1, \dots, 6$ (for $\log_2 R_n$ in place of $\log_2|\BLF(n)|$ the values are $-1.000, -0.708, -0.660, -0.666, -0.667, -0.651$).`

2. (Overstatement, Thm 7.1 Status) The 9 Nov cold read was of the earlier A22 text. The proof printed
   here was rebuilt on 21 Nov from that reader's step list and is read for the first time in this
   report. Replace the Status by:
   `\status{Paper. Origin: upper bound seat TB-O (R-116); lower bound from ChatGPT answer A22 (question Q22), checked by the project director and by an independent cold reader on 9 Nov 2026 (proved, three wording repairs; the reader recomputed $R_1, \dots, R_4$ three ways, checked the slice chain $\sum_{\text{good}}|\det A_B| \le$ simple vertices $\le R_\Sigma \le 2^kR_n$ for $n \le 5$ and $k \le 4$, and the moment bounds for $r \le 5$). The text above was rewritten on 21 Nov 2026 from that reader's step list, with the repairs included, and was cold read again on 23 Nov 2026 (proved, wording repairs applied). The bound is purely asymptotic: Theorem~\ref{thm:kks} gives no explicit $C$ or $n_0$. The linear term is open: ... (as in Issue 1).}`

3. (Proof repair, Thm 7.1 lower bound, first line) C need not be an integer. Replace "Fix $k = C$
   from Theorem~\ref{thm:kks} and put $r = d - k$." with:
   `Let $k = \lceil C\rceil$ with $C$ from Theorem~\ref{thm:kks}, put $r = d - k$, and take $n \ge k$, so that $r \ge 1$.`

4. (Wording, step (a)) Replace "so each $z_i$ lies in an open interval of length $2$, and at most two
   translates $t_j + \Z$ of each frozen value meet the projection of $P$. Each choice of translates
   cuts $P$ in a convex set, so a chamber meets $\Sigma$ in at most $2^k$ pieces, and the regions of the
   slice are exactly these pieces." with:
   `so each $z_i$ ($i \ge 1$) ranges over an open interval of length $2$ on $P$, which contains at most two points of $t_j + \Z$ for each frozen index $j$. For each choice of these points, $P \cap \{z_j = t_j + m_j,\ j \ge r\}$ is convex, and the projection is injective on $P$, so the chamber meets $\Sigma$ in at most $2^k$ connected open pieces. The complement of the walls in $\Sigma$ is the disjoint union of the open sets $\Sigma \cap C$ over the chambers $C$, so the regions of the slice are exactly these pieces.`

5. (Citation, steps (b) and Section 6 route 2) The slice arrangement is a shifted (non-central)
   toric arrangement. The vertex formula for it comes from Ehrenborg, Readdy and Slone, who allow
   rational normals and real constants and need regions that are open balls. As far as I could
   check (arXiv 0810.0295), this is ERS Theorem 3.6 with the reformulation in Theorem 3.11. I could
   not check that Moci's Corollary 5.16 covers non-central arrangements. Replace "By the vertex
   formula on $\Sigma$," with:
   `Since the normals $a_x$ span $\R^r$, the lifted regions of the slice are bounded and convex, so the regions are open cells, and the vertex formula \cite[Theorems~3.6 and~3.11]{ERS09}, which allows walls $a\cdot z \in c + \Z$ with real $c$, applies on $\Sigma$:`
   In Section 6 route 2, replace `\cite[Section~3]{ERS09}` with `\cite[Theorems~3.6 and~3.11]{ERS09}`
   after checking the numbering against the published version.

6. (Citation, Thm 7.2) In arXiv:1808.07222 the KKS statement is Theorem 1.7, and it uses
   $d_\pm(\mathrm{span}) > \log_2(2r)$, which is equivalent to "more than $2r$ vectors" as stated. I
   could not check the CPC numbering (Theorem 1.6). Either check it, or write
   `\cite[Theorem~1.6]{FJZ22} (Theorem~1.7 in the arXiv version)`.

7. (Gap, Prop 8.1) Lemma 4.1 gives every output-affine class at bit $j$. $j^*(n)$ concerns every
   function, so the closure at a fixed bit is needed. The same remark is needed for the Section 6
   sentence "bit $n-1$ reaches every class". After "Lemma~\ref{lem:grid} applies with $q = 2^j$ as
   soon as $2^j > (n+1)(n+2)^{(n+2)/2}/2$" insert:
   `; since adding $2^j$ to $K$ or to $a_i$ XORs bit $j$ of $K + a\cdot x$ with $1$ or with $x_i$, the set of functions realized at a fixed bit $j$ is a union of output-affine classes, so reaching every class at bit $j$ means reaching every function`
   Also change "The values for $n \le 6$ are those of Section~\ref{sec:counts}." to:
   `The values for $n \le 6$ are those of Section~\ref{sec:counts}; failure at bit $n-2$ implies failure at every smaller bit, since bit $j$ of $N$ is bit $j+1$ of $2N$.`

8. (Overstatement, after Prop 8.1) Announced results are explicitly not claimed. Replace "The truth
   is close to the upper bound: Announced result~\ref{ann:ah} below gives $j^*(n) = \frac12 n\log_2 n -
   n + o(n)$." with:
   `If Announced result~\ref{ann:ah} below holds, then $j^*(n) = \frac12 n\log_2 n - n + o(n)$, close to the upper bound.`

9. (Records) The bit $n-2$ class counts $1, 5, 164, 22067$ ($n = 2, \dots, 5$) and the universality
   of bit $n-1$ for $n = 2, 3, 4$ are not in results/runs_21nov.txt. Only $n = 6$ (q = 16, 32) and
   $n = 5$ (q = 16) are recorded. They are reproducible with compute/grid.c: I ran `grid 3 2` (5),
   `grid 4 4` (164), `grid 5 8` (22067), `grid 3 4` (13) and `grid 4 8` (324). Suggest appending a line
   to runs_21nov.txt:
   `grid n 2^(n-2) (bit n-2): classes 1, 5, 164, 22,067 (n = 2..5); grid n 2^(n-1) (bit n-1): 2, 13, 324, 29,747 (n = 2..5) = all classes`

10. (Status definition, Section 1) "Computer means ... reproduced by an independent reader's own
    code" holds for $n \le 5$. It does not hold, as far as the repository shows, for $R_6$, the 1000
    orbits at $n = 6$, Prop 6.2 at $n = 6$, or 9449818. Those rest on the project's three routes. I
    reproduced all the $n \le 5$ numbers but none at $n = 6$. Replace the sentence with:
    `\emph{Computer} means an exhaustive computation in exact integer arithmetic, made complete by a proved reduction; for $n \le 5$ every such number was reproduced by an independent reader's own code, and the $n = 6$ numbers rest on the three independent routes of Section~\ref{sec:counts}.`

11. (Wrong item, Cor 5.3 proof) Replace "The list follows from Theorem~\ref{thm:small}(1), by
    enumeration." with:
    `The list follows by enumerating $\BLF(3)$ (Theorem~\ref{thm:small}(1) and~(2)).`

12. (Abstract overstatement) The input symmetries are paper only. Replace "the general closure
    properties, the counts for $n \le 4$ and the structure for $n \le 4$ are proved in Lean~4 with
    Mathlib" with:
    `the parallelogram inequality, the inclusion of threshold functions, closure under XOR with affine functions, the counts for $n \le 4$ and the structure for $n \le 4$ are proved in Lean~4 with Mathlib`

13. (Status, Prop 2.3) `BLF.threshold_isBLF` takes integer weights. Replace "(integer weights;
    every threshold function has an integer realization)" with:
    `(integer weights; the real case follows because every threshold function has an integer realization, Lemma~\ref{lem:weights}, which is not formalized)`

14. (Notation, Thm 5.1 outline) $w$ names both a vertex and the weight vector. Replace "for every affine
    $\ell$ one of eight explicit parallelograms $x + y = z + w$ carries the values $1, 1, 0, 0$ ...
    $w_0 + w\cdot w > 0$." with:
    `for every affine $\ell$ one of eight explicit parallelograms $x + y = z + z'$ carries the values $1, 1, 0, 0$ of bit $1$ of the sum XOR $\ell$, which no threshold function can do: $w_0 + w\cdot x > 0$ and $w_0 + w\cdot y > 0$ force $w_0 + w\cdot z > 0$ or $w_0 + w\cdot z' > 0$.`

15. (Cross-reference, Introduction item 5) Replace "in particular threshold XOR affine functions form
    a vanishing share of BLF." with:
    `in particular threshold XOR affine functions form a vanishing share of BLF (Corollary~\ref{cor:share}).`

16. (Precision, Cor 7.3 proof) Cover counts dichotomies of points in general position. For the cube
    vectors the count is only an upper bound. Replace "so there are at most
    $2\sum_{i=0}^{n}\binom{2^n-1}{i}$ of them \cite{Cover65}," with:
    `so there are at most $2\sum_{i=0}^{n}\binom{2^n-1}{i}$ of them (the number for $2^n$ vectors in general position in $\R^{n+1}$ \cite{Cover65}, an upper bound for the region count of any central arrangement of $2^n$ hyperplanes in $\R^{n+1}$),`

17. (Notation, Lemma 4.1) $(\Z/q)^n$ reads as $(\Z/q\Z)^n$. Replace "a point $(t, r)$ with
    $r \in (\Z/q)^n$ and $t \in \Z/q$" with `a point $(t, r)$ with $r \in (\tfrac1q\Z)^n$ and $t \in \tfrac1q\Z$`,
    and "$\Z/q$" in the proof with `$\tfrac1q\Z$`.

18. (Grammar and repository, Section 10) Replace "of Section~\ref{sec:char} and~\ref{sec:reductions}"
    with `of Sections~\ref{sec:char} and~\ref{sec:reductions}`. The Section 7 proof and its cold reads
    (COLD_READ_Q22.md and this report) are not in the repository. Suggest adding them as coldread/Q22/
    and changing the sentence to
    `\texttt{proofs/} and \texttt{coldread/} hold the proofs of Theorem~\ref{thm:identity} and of Sections~\ref{sec:char} and~\ref{sec:reductions}, and the cold reads of Section~\ref{sec:asym}, with the readers' reports and code.`

19. (Credits, Section 10) CR-O appears only in the credits, while CAF-O, CAS-O and RC-O (Status of
    9.2) are missing. Replace "Seats BL-O, BL6-O, TB-O, CR-O, AH-O, CK-O and the cold readers" with
    `Seats BL-O, BL6-O, TB-O, CR-O, AH-O, CAF-O, CAS-O, CK-O, RC-O and the cold readers`.

20. (Minor, abstract and intro "for $n \le 3$") Theorem 5.1(2) states only $n = 3$. Append to
    Theorem 5.1(2): `(For $n \le 2$ every Boolean function is threshold XOR affine and BLF.)`

21. (Missing step, Thm 7.1 step (d)) Replace "which is less than half of the lower bound for
    $\mathbb{E}Z$ once $n \ge n_0$." with:
    `which is less than half of the lower bound for $\mathbb{E}Z$, hence less than $\frac12\mathbb{E}Z$, once $n \ge n_0$; so $\mathbb{E}[Z\mathbf{1}_{\text{good}}] \ge \frac12\mathbb{E}Z$.`

22. (Minor, step (c)) Replace "so $|\gamma_j| \le (r+1)^{(r+1)/2} \le H$" with
    `so $|\gamma_j| \le (r+1)^{(r+1)/2} \le H$ by Hadamard's inequality (each row has norm at most $\sqrt{r+1}$)`.

## Status lines against the repository

- Lean: all ten names in Section 10 exist in Challenge.lean and Solution.lean with the stated
  meaning. They are listed in comparator.json, with no sorry or native_decide in Solution.lean or
  BLF/*.lean. `BLF.search_sound` is in BLF/Search.lean. `decide +kernel` is used in the data and
  Strict files. The eight parallelograms of the outline are `Strict.L`. review/lean1 and
  review/lean2 contain the axiom, non-vacuity and planted-error checks.
- Thm 3.4 Status: matches coldread/R116 (verdict, nine issues, 15456 pairs).
- Lemma 4.1, 4.2 Status: matches coldread/R096 (own maxdet.c; q = 55 grid, the "different grid" of
  Thm 5.2).
- Thm 7.1 Status: Issues 1 and 2. The 9 Nov reader's numbers (slice chain, moments) agree with
  COLD_READ_Q22.md and with my recomputation.
- Every number in Sections 4 to 6 agrees with results/runs_21nov.txt, except the unrecorded ones in
  Issue 9.

## What I recomputed (own code in /home/claude/coldread_paper/code)

- bitclasses.c: classes reached at bit j, with K, a_i in [0, 2^j). Bit n-2 gives 1, 5, 164, 22067
  (n = 2..5). Bit n-1 gives 2, 13, 324, 29747 (n = 2..5), equal to (R_n+1)/2. Bit n gives the same,
  and bit 5 at n = 5 also gives 29747. So j*(n) = n-1 for n <= 5, and R_2..R_5 = 3, 25, 647, 59493
  via Theorem 3.4.
- thr5.c, thr5b.c: thresholds 104, 1882, 94572 (weights up to 22, and also up to M_5 = 18). TXA
  classes are 13, 323, 25997, with no TXA class outside BLF. There are 3750 extra classes at n = 5 in
  15 orbits of sizes {1, 5, 32, 32, 80, 80, 160, 160, 160, 320, 320, 320, 480, 640, 960} (sum 3750).
  The orbits of all classes number 4, 12, 66 for n = 3, 4, 5 (TXA orbits 4, 11, 51).
- Arithmetic: 25997 x 64 = 1663808 and 3750 x 64 = 240000. Shares are 10336/10368 = 99.69% and
  1663808/1903808 = 87.39%. The table entries (R+1)/2 and 2^n(R+1) check for n = 0..6.
- ca_and_D.py: BLF(3) = 208, 88 CA classes, 73 BLF, the 15 listed non-BLF classes, no mixed class,
  and Rule 110 is BLF. For n = 1..4, D_n = 1, 4, 60, 3360, bases 1, 4, 58, 3008, and
  sum det^2 = m^d/4^n exactly.
- moments.py: E Z^2 = r! and E Z^4 = 1, 8, 96, 2112 against the bound 3, 24, 360, 8640. E Z is
  above the Hoelder bound for r <= 4.
- slicecheck.py, slicecheck2.py: step (c) checked literally, with the paper's t_j = L^{-j} and
  H = (r+1)^{r+1}, for (n,k) = (2,1), (3,1), (3,2), (4,1), (4,2), (4,3). No good set has a non-simple
  vertex. sum_good |det A_B| <= simple vertices <= R_Sigma (NBC vertex sum) <= 2^k R_n:
  4, 4, 4 <= 6; 8, 8, 26 <= 50; 16, 16, 16 <= 100; 96, 112, 520 <= 1294; 112, 112, 220 <= 2588;
  64, 64, 64 <= 5176.
- β ratios (Issue 1) from the R_n values.
- compute/grid.c run for the unrecorded bit counts (Issue 9).
- Not recomputed: anything at n = 6 (R_6, D_6, the 1000 orbits, 9449818), and the Lean build.

## Sources consulted for citations

- ERS, arXiv 0810.0295: toric hyperplanes have rational normals and real constants; the region
  count is Theorem 3.6 and Theorem 3.11 (needs regions that are open balls).
- Ferber, Jain, Zhao, arXiv 1808.07222, Theorem 1.7: the KKS statement as used.

# The toric identity |BLF(n)| = 2^n (R_n + 1)

Rebuilt 21 Nov 2026 (Claude Opus 5.5, for team LKC01-T00316), from the statement in the ledger; the
original TB-O proof is lost. Status: proved, cold read 21 Nov 2026 by an independent reader (verdict:
proved, wording repairs only; repairs 1 to 9 applied below; report and code in coldread/).

## 1. Setting

Here BLF(n) is the set of maps x -> bit j of (K + a.x) on {0,1}^n with j >= 0 and K, a_1, ..., a_n
integers, with no bound on j or on the bit width. For a negative integer N, bit j of N means
floor(N / 2^j) mod 2 (two's complement); by (F1) below, allowing negative K or a_i gives the same set as
requiring them nonnegative.

For a real affine function u(x) = t + r.x on {0,1}^n write F_u(x) = floor(u(x)) and f_u = F_u mod 2.
Call u generic if u(x) is not an integer at any cube vertex. Let Lambda be the integer affine functions
(t, r in Z^(n+1)); identify u with the point (t, r) of R^(n+1).

Facts used throughout.

(F1) For m in Lambda, F_(u+m) = F_u + m on the cube, so f_(u+m) = f_u XOR (m mod 2), and m mod 2 is a
GF(2)-affine function. Every GF(2)-affine function arises this way.

(F2) For generic u, floor(-u(x)) = -F_u(x) - 1, so f_(-u) = f_u XOR 1.

(F3) For any u and any e > 0 smaller than the distance from each non-integer u(x) up to the next integer, F_u = F_(u+e) on the cube (floor is right continuous) and u + e is generic.

**Proposition 1 (R-096, characterization).** f is BLF iff f = f_u for some real affine u.

Proof. If f = bit j of K + a.x, take u = (K + a.x)/2^j. Conversely, by (F3) we may take u generic. The set
{u' : F_(u') = F_u} is open in R^(n+1) (strict inequalities F_u(x) < u'(x) < F_u(x) + 1) and nonempty, so it
contains a point (K, a)/2^j with integers K, a and some j. Then f_u = bit j of K + a.x. (Negative a_i
or K are allowed; adding multiples of 2^(j+1) makes them nonnegative without changing bit j, by (F1).)

## 2. Chambers

The toric arrangement is {p in T^(n+1) = R^(n+1)/Z^(n+1) : v_x . p in Z} with v_x = (1, x),
x in {0,1}^n. Its chambers are the connected components of the complement; R_n is their number.

**Lemma 2.** Chambers correspond bijectively to the sets F_u (u generic) modulo Lambda (restricted to the
cube).

Proof. For a realizable integer function F on the cube, the region P_F = {u : F_u = F} is an
intersection of open slabs, hence convex and connected, and the regions P_F partition the generic points
of R^(n+1); they are exactly the connected components of the complement of the periodic arrangement
{u : u(x) in Z}. Translation by m in Lambda (= Z^(n+1)) maps P_F to P_(F+m), and P_(F+m) = P_F only
if m vanishes on the cube, which forces m = 0 since the cube affinely spans R^n. The projection to the
torus therefore maps each Lambda-orbit of regions onto one chamber, injectively on each region. The preimage in R^(n+1) of the complement of the toric arrangement is the
set of generic points, and the projection is a covering map. The image of a region P is open and
connected; its preimage is the union of the translates P + m, which is closed in the generic set (its
complement there is a union of other regions), so the image is also closed in the complement on the
torus and is therefore a whole chamber. Two regions with the same image intersect after a translation,
hence lie in one Lambda-orbit. []

By (F1), the output-affine class of f_u depends only on the chamber of u. By (F2), u and -u give the
same class. Call chambers C and -C antipodal.

## 3. The core lemma

**Lemma 3.** Let u, w be generic with f_u XOR f_w GF(2)-affine. Then F_w is in F_u + Lambda or in
-F_u - 1 + Lambda; that is, w lies in the chamber of u or in the chamber of -u.

Proof. By (F1) replace w by w + mu (mu in Lambda lifting the affine difference); this keeps its
chamber, and now F_u = F_w (mod 2) at every vertex. Write F = F_u, G = F_w and
a(x) = u(x) - F(x), c(x) = w(x) - G(x), both in the open interval (0, 1) by genericity.

*Carries.* Fix a direction i and write u_i = k_i + alpha_i, w_i = m_i + beta_i with k_i, m_i integers
and alpha_i, beta_i in [0, 1). Along an edge x -> x + e_i,

  F(x + e_i) - F(x) = k_i + A_i(x),  G(x + e_i) - G(x) = m_i + C_i(x),

where A_i(x) = [a(x) + alpha_i >= 1] and C_i(x) = [c(x) + beta_i >= 1] are the carries, and
a(x + e_i) = a(x) + alpha_i - A_i(x), c(x + e_i) = c(x) + beta_i - C_i(x).

*Type of a direction.* F = G mod 2 gives A_i(x) - C_i(x) = m_i - k_i (mod 2) on every i-edge, a parity
independent of x. Call i of type S if A_i = C_i on every i-edge, and of type D if A_i = 1 - C_i on every
i-edge. Every direction has exactly one type. Call i rigid if A_i is constant on the i-edges.

*Step 1 (mixed faces).* Let i have type S and j type D, and fix a 2-face x, x + e_i, x + e_j,
x + e_i + e_j. Write kappa = A_i(x), kappa' = A_i(x + e_j), lambda = A_j(x), lambda' = A_j(x + e_i).
Computing floor(u(x + e_i + e_j)) - floor(u(x)) along the two paths gives
kappa + lambda' = lambda + kappa'. Doing the same for w, with C_i = A_i and C_j = 1 - A_j, gives
kappa + (1 - lambda') = (1 - lambda) + kappa'. Adding: kappa = kappa'; then lambda = lambda'.
So A_i is invariant under flipping any coordinate of type D, and A_j under flipping any coordinate of
type S.

*Step 2 (two auxiliary functions).* Let I_S, I_D be the sets of directions of each type and write
x = (x_S, x_D). Put g(x) = a(x) + c(x) - 1 and h(x) = a(x) - c(x). Along an i-edge with i in I_S,
g changes by alpha_i + beta_i - 2 A_i(x) and h by the constant alpha_i - beta_i. Along a j-edge with
j in I_D, g changes by the constant alpha_j + beta_j - 1 and h by alpha_j - beta_j - 2 A_j(x) + 1.
By Step 1, A_i (i in I_S) depends on x_S only and A_j (j in I_D) on x_D only. Summing along a path that
first changes the S-coordinates and then the D-coordinates,

  g(x) = g_S(x_S) + L_D(x_D),  h(x) = h_D(x_D) + L_S(x_S),

with L_S, L_D linear. Since a, c are in (0, 1), at every vertex

  |g(x)| + |h(x)| < 1.                                                              (*)

Indeed |g| + |h| = max(|g + h|, |g - h|) = max(|2a - 1|, |2c - 1|).

*Step 3 (the 16-vertex count).* Suppose some i in I_S and some j in I_D are both non-rigid.
Since A_i depends on x_S only and x_i = 0 on i-edges, A_i is a function on the cube
{0,1}^(I_S minus {i}). It is not constant, and a non-constant function on a cube changes along some
edge; this gives k in I_S, k != i, and a point x with A_i(x) != A_i(x + e_k). Let Q_S be the 2-face of
{0,1}^(I_S) spanned by e_i, e_k at x_S. The second difference of g_S over Q_S is the difference of the
two i-increments, -2(A_i(x + e_k) - A_i(x)) = +-2, and because A_i does not depend on x_D it is the same
+-2 over Q_S x {x_D} for every x_D. Likewise there is a 2-face Q_D in two D-directions on which the
second difference of h_D is +-2. Consider the 16 vertices (x_S, x_D) with x_S in Q_S and x_D in Q_D.

For fixed x_D, g restricted to Q_S is g_S plus a constant, so its second difference is +-2, and the
triangle inequality gives sum over x_S in Q_S of |g| >= 2. Summing over the four x_D:
sum over the 16 vertices of |g| >= 8.

For fixed x_S, likewise sum over x_D in Q_D of |h| >= 2, and by (*) sum over x_D of |g| < 4 - 2 = 2.
Summing over the four x_S: sum over the 16 vertices of |g| < 8. Contradiction.

So all directions of type S are rigid, or all directions of type D are rigid.

*Step 4 (conclusion).* Put S = (F + G)/2 and D = (F - G)/2, integer valued since F = G mod 2.
For i in I_S, D(x + e_i) - D(x) = (k_i - m_i)/2 is constant and S(x + e_i) - S(x) = (k_i + m_i)/2 + A_i(x);
for j in I_D, S(x + e_j) - S(x) = (k_j + m_j + 1)/2 is constant and
D(x + e_j) - D(x) = (k_j - m_j - 1)/2 + A_j(x), which is constant when j is rigid. If every type-D direction is rigid, then D has
constant steps in every direction, so D is affine with integer values, hence in Lambda on the cube, and
G = F - 2D is in F + Lambda: w is in the chamber of u. If every type-S direction is rigid, S is in
Lambda, and floor(-w) = -G - 1 = F - 2S - 1 is in F + Lambda: w is in the chamber of -u. The "or" of Step 3 covers the cases I_S or I_D empty.
Since the shift w -> w + mu in the first line does not change the chamber of w, the same conclusion
holds for the original w. []

(Sharpness: equality 8 = 8 is excluded only by the strict inequalities in (*), i.e. by genericity.)

## 4. The count

**Lemma 4.** Exactly one chamber is its own antipode: the chamber of the constant u = 1/2.

Proof. The arrangement is invariant under p -> -p, so negation maps chambers to chambers, and -P is a
region lifting -C. If -C = C, a lifted region P satisfies -P = P + m for some m in Z^(n+1), so P is invariant
under the point reflection y -> -y - m and, being convex, contains its centre -m/2. A half-integer point
(m_0, m_1, ..., m_n)/2 is generic iff m_0 + m.x is odd for every x, i.e. m_0 odd and every m_i even;
modulo Z^(n+1) this is the single point (1/2, 0, ..., 0). Conversely that point is fixed by p -> -p. []

In particular the other chambers pair off, so R_n is odd.

**Theorem 5 (R-116).** The output-affine classes of BLF(n) correspond to the antipodal pairs of chambers,
the self-antipodal chamber counting once. Hence there are (R_n + 1)/2 classes and

  |BLF(n)| = 2^(n+1) (R_n + 1)/2 = 2^n (R_n + 1).

Proof. By Proposition 1 and (F3) every BLF function is f_u for a generic u; by (F1) and (F2) the class
map from chambers is well defined and constant on antipodal pairs; by Lemma 3 it separates distinct
pairs. Each class is a coset of the 2^(n+1) GF(2)-affine functions, and BLF(n) is a union of classes by
(F1). Lemma 4 gives (R_n - 1)/2 + 1 pairs. []

## 5. Machine checks (this rebuild)

R_n values are confirmed by two independent methods (universal grid and no-broken-circuit formula);
grid counts alone are lower bounds unless the grid is proved universal.

- Chambers counted directly on the universal grid (chambers.c): R_1..R_5 = 1, 3, 25, 647, 59,493, and in
  each case the number of distinct classes is exactly (R_n + 1)/2.
- R_n by the vertex (no-broken-circuit) formula, no grid (nbc.c): same values for n <= 5, and
  R_6 = 21,238,195 (D_6 = 549,734,400), equal to the q = 32 grid chamber count, so that grid meets every
  chamber and |BLF(6)| = 64 (R_6 + 1) = 1,359,244,544.
- Cold reader (independent code, coldread/): R_1..R_5 and classes (R + 1)/2 again; at most 2 chambers per
  class, always antipodal; Lemma 3 and every intermediate claim checked in exact arithmetic on 15,456
  pairs with affine XOR for n = 2..6 (random, collision grouping, adversarial hill climb): 0 failures.
- Universal grids: largest (n+2)-minor of the rows (1, x, +-1) is 2, 4, 6, 10, 18 for n = 1..5 (exhaustive,
  maxminor.c), so q > (n+1) Delta / 2 suffices; q = 16, 32, 64 for n = 3, 4, 5.

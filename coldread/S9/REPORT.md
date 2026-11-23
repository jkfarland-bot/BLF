# Cold read of Section 9, "Cellular automata in few arithmetic operations"

Reader: an independent cold reader (a Claude agent) who did not write the section. Sources read:
`/home/claude/coldread_s9/section9.tex` and `/home/claude/coldread_s9/blf_full.pdf` (for (1), Proposition 2.1,
(F1) to (F3) and Corollary 5.3). I did not open `compute/ca_ops.py` or any other project file. All code is my own,
written from the text, and is in `/home/claude/coldread_s9/code/`. Run it with `code/run_all.sh`. The outputs are
in `code/outputs.txt` and are quoted below. Everything is Python, single thread, under 1.5 minutes in total
(the optional probe with M < 2^17 took 2.5 minutes more).

## Verdicts at a glance

| Item | Verdict |
|---|---|
| 1. Model paragraph | proved after a wording repair (bitwise operations on negative integers are not defined) |
| 2. Lemma 9.1 | proved after a wording repair (the second case, "exchange the roles of V and V'", line 67) |
| 3. Proposition 9.2 | proved; one loose phrase ("handled as before", line 88). The excluded case is the only gap, and the method cannot close it |
| 4. Corollary 9.3 | proved |
| 5. Proposition 9.4 and Theorem 9.5 | proved after a wording repair (the statement of Proposition 9.4 does not say that b and pi are chosen) |
| 6. Closing paragraph | proved after a wording repair (programs of one operation are not mentioned; the sentence is hard to parse) |

I found no mathematical error. Every computation agrees with the text.

---

## 1. Model paragraph (lines 22 to 35)

**Verdict: proved after a wording repair.**

* "A bit-field encoding is an integer affine function of the cells" (line 31). This is correct. If bit e is
  either a constant k_e in {0,1} or the value x_{c(e)}, then X = sum_e k_e 2^e + sum_i a_i x_i with
  a_i = sum over {e : c(e) = i} of 2^e. The sum is finite because X is a nonnegative integer. A clause giving
  this reason would help. In E(x) with b > pi + 1, slot i has bit 0 equal to 1, bit pi equal to x_i, and every
  other bit 0. The slots are disjoint.
* **Precision gap (lines 32 to 34).** The bitwise operations are listed with c >= 0, but the text never says
  what they do to a negative Y. Negative values do arise: Y + c and cY allow c < 0, and Proposition 9.2 then
  applies a bitwise operation to them. The intended meaning (bit by bit on the bits floor(Y/2^e) mod 2, which is
  two's complement) is implicit in "Bit e of an integer Y is ...". **Fix:** after the list of operations add
  "The bitwise operations act bit by bit on these bits; for Y < 0 this is two's complement."
* Line 25, "k steps of a rule of radius R form one table with r = 2kR+1 and o = kR". This holds on cyclic rows of
  every length, N < r included, because a cyclic row evolves like its periodic extension; the window then repeats
  cells. Theorem 9.5 is claimed for every N >= 1, so one clause would help: "(for N < r the window wraps around
  and repeats cells)". I checked this directly: my Theorem 9.5 test compares with step-by-step simulation, not with
  g on wrapped windows, for N = 1 to 10.
* Optional notation clashes. b is the slot width but also b_*, b_i in Lemma 9.1 and Corollary 9.3. M is the
  multiplier but also a maximum in Lemma 9.1. m is the number of windows but also a pattern in Theorem 9.5.
  c is a constant, a cell, a coefficient vector and a slot index. K is a constant and K_m a complete graph.

## 2. Lemma 9.1 (lines 37 to 68)

**Verdict: proved after a wording repair.**

The steps checked:

* floor(A/D) = B + floor(Phi) with b_i = floor(a_i/D) and s_i = a_i/D - b_i in [0,1). Correct.
* Bins and bad pairs. Two disjoint bad pairs for one bin would have disjoint unions, each holding more than half of
  that bin's cells, which is impossible. A family of pairwise intersecting edges is a star or lies in a triangle.
  Correct.
* Counting. The star families do not cover any edge among the kappa vertices that are not centres, so those
  C(kappa,2) edges lie in the 2r - alpha other families, each with at most 3 edges. With
  C(kappa,2) - 3(kappa-2) = (kappa-3)(kappa-4)/2 >= 0 (the identity checks), this gives
  kappa - 2 <= 2r - alpha, and kappa >= m - alpha gives m <= 2r + 2. Correct, including when alpha > m.
  This step is tight. With m = 2r + 2, take 2r - 1 bins that put all their cells in one window each (stars
  centred at V_1, ..., V_{2r-1}) and one bin that spreads its cells equally over the last three windows (a
  triangle). Then every pair is bad (checked for r = 1 to 5). So the hypothesis floor(N/r) >= 2r + 3 is
  exactly what this counting needs.
* Partners. A pair that is good for every bin has at most half of each bin's cells in V u V', so within each bin
  there is an injection into the cells outside. Bins are half open, so |s_c - s_c'| < 1/(2r). Correct.
* Restriction. Phi = Phi_0 + sum (s_c - s_c') x_c, and each part has range sum |d_c| < r/(2r) = 1/2. Correct.
* Intervals. I u I' is the closed interval [Phi_0 + mu + mu', Phi_0 + M + M'] of length less than 1, so it holds
  at most one integer n. If n is in I, then I' lies in [n, n+1) and floor is constant on I'. Otherwise no integer
  lies in (left end of I, right end of I], and floor is constant on I. Correct, including n at the shared
  endpoint.
* First case. With x_V at a maximizer and x_V' free, Phi stays in I'. So floor(A/D) = B + const is integer
  affine in x_V'. Every cell outside V' is either constant (V, the partners of V, the other cells) or the
  complement of a cell of V' (the partners of V'). Correct.
* **Wording problem, line 67:** "in the second, exchange the roles of V and V'." In the second case the proof
  needs x_V' to stay at the *minimizer* of the V' part that defines I, with x_V free; V is then the window of
  the statement. Suppose the sentence is read as the mirror image of the previous one ("fix x_V' at a maximizer
  of the V' part"). Then it is false. Example: r = 1, both parts range over [0, 0.4], Phi_0 = 0.5. Then
  I = [0.5, 0.9] and I' = [0.9, 1.3], so the integer 1 lies in I' only. With x_V' at a maximizer, Phi ranges
  over [0.9, 1.3] and floor is not constant. In my runs this reading failed in 399 of 7094 second-case
  instances, while the intended reading never failed. Read instead as "repeat the argument with V and V'
  exchanged", the step is circular, because the repeat can land in its own second case.
  **Fix:** "In the first case fix x_V at a maximizer of the V part and take V' as the window. In the second,
  keep x_V' at the minimizer used to define I and let x_V vary; then V is the window of the statement."
* Minor: the proof does not need D to be an integer. "Integer coefficients" is what makes A, restricted to the
  rows, integer affine in x_V'. Proposition 9.2 uses that fact.

## 3. Proposition 9.2 (lines 70 to 90)

**Verdict: proved.** One loose phrase needs repair. The excluded case is the only gap.

Write Aff = {Y + c, cY}, Bit = {and, or, xor with c >= 0}, Fl = floor, Rem = remainder. All 7 x 7 pairs
(phi_1, phi_2) fall into the cases below, except (Fl, Rem) and (Rem, Rem).

* **phi_1 in Aff or Bit.** Y_1 is integer affine. For Bit, X >= 0 and c >= 0, so Y_1 is a finite sum of literals
  (x or 1 - x) times powers of 2. Correct.
  * phi_2 in Aff: Y is integer affine in all cells. Fixing the cells outside the window of j needs the window to
    hold r distinct cells (N >= r). Then Proposition 2.1, which allows negative K and a_i, shows g is BLF.
    Correct.
  * phi_2 in Bit: here Y_1 can be negative (phi_1 = Y + c with c < 0, or cY with c < 0). In two's complement,
    bit e of (Y_1 op c) is a constant, bit e of Y_1, or its negation. This is correct once the item 1 repair
    defines the bitwise operations for negative Y.
  * phi_2 in Fl or Rem: apply Lemma 9.1 to Y_1 (integer coefficients, possibly negative, which the lemma allows).
    On its rows, Y_1 and floor(Y_1/D) are both integer affine in x_V', so Y_1 - D floor(Y_1/D) is too. The cell
    whose window is V' is j = v + o, where v is the first cell of V'. Correct.
* **phi_1 in Fl or Rem.** Apply Lemma 9.1 to X. Then Y_1 = Lambda is integer affine in x_V' on the rows (and
  Lambda >= 0).
  * phi_2 in Aff or Bit: correct, but "is handled as before" (line 88) is loose. "Before" meant fixing the cells
    outside the window, and that does not apply here, because Y_1 is not affine in all cells. **Fix:** "an affine
    or bitwise phi_2 gives, at the cell whose window is V', a bit of an integer affine function of x_V', possibly
    negated, or a constant".
  * phi_2 = Fl: floor(floor(Lambda/D)/2^e) = floor(Lambda/(2^e D)), since 2^e and D are positive integers, and
    this is f_u for u = Lambda/(2^e D). Correct. Checked exhaustively for r = 3 and small coefficients: 0 failures.
* **Negated read bit:** adding 2^e to K flips bit e for every integer value, negative ones included, because
  floor((Z + 2^e)/2^e) = floor(Z/2^e) + 1. Correct.
* **The excluded case is the only gap, and it is a real gap for this method.** After the lemma, the intermediate
  value is an integer affine Lambda of the r cells of one window, and no free cells are left for a second
  lemma. A bit of Lambda mod D need not be BLF. Example: Lambda = 1 + z_0 + z_1 + 2 z_2 and D = 5. Bit 2 of
  Lambda mod 5 is z_2 and (z_0 xor z_1), the table of elementary rule 40, which is not BLF (its class is in the
  list of Corollary 5.3, and my enumeration of BLF(3) confirms it). This does not show that some program of that
  shape computes a non-BLF table at every cell. It only shows that the one-window argument cannot be extended
  to that shape. The text states the exclusion honestly.
* **Hypothesis.** floor(N/r) >= 2r + 3 is exactly the lemma's hypothesis, applied with the same r and N. N >= r
  is needed only in the first case (fixing the outside cells) and follows from the hypothesis. I found no other
  use.
* Optional strengthening: the proof never uses c >= 0 or the specific affine maps. It works unchanged for every
  integer affine map Y -> alpha Y + beta (so c - Y counts as one operation) and for bitwise operations with any
  integer constant, NOT (xor with -1) included. For X op c with c < 0, every bit is still a constant or a
  literal, and Y_1 = -2^T + (finite sum) is integer affine. Saying so would strengthen the lower bound in the
  closing paragraph.

## 4. Corollary 9.3 (lines 92 to 108)

**Verdict: proved** (also Lean-checked according to the status line).

* With a_l = 2^j b_l + s_l, the rise of G along an edge is in {0, 1} and equals
  f(x) xor f(x + e_l) xor (b_l mod 2). Correct.
* The two paths across a square have equal totals. I derived both cases by hand. Pattern 0,1,1,1 gives
  (1 - beta_r) + beta_{r-1} = (1 - beta_{r-1}) + beta_r, so beta_{r-1} = beta_r. Pattern 0,1,0,0 gives
  2 - beta_r - beta_{r-1} = beta_{r-1} + beta_r, so beta_{r-1} != beta_r. Checked exhaustively for j <= 4:
  149,792 cases, no failure.
* Window values, from my own composition of Rule 110:
  * two steps, 00000 to 00011: 0,1,1,1; 01000 to 01011: 0,1,0,0
  * three steps, 0000000 to 0000011: 0,1,1,1; 0010000 to 0010011: 0,1,0,0

  All as stated.
* Bounds: floor(N/5) >= 13 if and only if N >= 65, and floor(N/7) >= 17 if and only if N >= 119; 256 satisfies
  both.
* Minor: the proof numbers the inputs 1..r (b_{r-1}, b_r), as in (1), while the Model and Proposition 9.4 number
  them 0..r-1 (c_d with d < r). **Fix:** say "(inputs numbered 1 to r as in (1))", or write b_{r-2}, b_{r-1}.

## 5. Proposition 9.4 and Theorem 9.5 (lines 113 to 170)

**Verdict: proved after a wording repair.**

* **Field identity.** The expansion of F_i is correct. The low part is
  sum c_d <= r(2^{l+1} - 1) < 2^pi. floor(F_i / 2^pi) = K + sum c_d x_{i+d} + 2^pi K x_i, and 2^{l+1} divides
  2^pi, so bit pi + l of F_i is h. Correct. "pi > l" already follows from 2^pi > 2^{l+1}(r+1).
* **Bound.** F_i <= sum c_d + 2^pi (K + sum c_d) + 2^{2pi} K < 2^{pi+l+1} + 2^{2pi+l+1} < 2^{2pi+l+2}. Every term
  is nonnegative and every v is at most 1 + 2^pi, so any sub-sum of terms, with any cells' v, obeys the same
  bound. Correct. My code builds the slots from the definition, compares them with the product, and asserts the
  bound. The largest slot measured was 0.4632 * 2^{2pi+l+2}.
* **Slot width.** b = 2pi + l + 3 is one more than needed (2pi + l + 2 is enough), and it satisfies b > pi + 1.
  Fine.
* **Replication.** P = ceil((r-1)/N) + 1 gives PN >= N + r - 1, so slot r + i receives all r terms
  (c = i + d <= N + r - 2 < PN). Correct, including N = 1, where P = r.
* Line 147, "receives sum c_d v_c + ... over the pairs c - d = s - r with c < PN": the "+ ..." should be spelled
  out. **Fix:** "receives sum c_d v_c over the pairs (c, d) with c - d = s - r and 0 <= c < PN, plus 2^pi K v_{s-r}
  when 0 <= s - r < PN (indices of v modulo N)".
* **beta.** Nonzero slots run from 1 to PN + r - 1, so the product is below 2^{t + b(PN + r)}, and
  beta = b(r + PN + 1) is a safe bound. Correct.
* **Block spacing.** Offsets are k G + rho with G = bN ceil(beta/(bN) + 1) >= beta + bN and 0 <= rho < bN. So two
  blocks differ by at least beta + 1 > beta. Correct, and asserted in my code.
* **h_m.** Q(z) = 2^L - |m| + sum (2m_d - 1) z_d lies in [2^L - r, 2^L], which is inside [1, 2^L], and equals 2^L
  only at z = m, so bit L of Q is [z = m]. After reduction modulo 2^{L+1}, K lies in [0, 2^L] and each c_d is
  1 or 2^{L+1} - 1. Correct.
* **Residues.** The block of m needs t = b(o - r) - L (mod bN), and the extra block needs t = b(o - r) (mod bN).
  Both are as described. Correct.
* **Final reduction.** 2^{bN} = 1 (mod D). The exponents bj and bj + pi are distinct modulo bN (0 < pi < b), and at
  most one m matches each window, so the folded sum is E(y). Correct. E(y) < D also holds: the construction has
  pi >= 4, so bit 1 of every slot is 0. But the Model allows pi = 1, where bit 1 is x_i, so the stated reason
  depends on the choice of pi. **Fix:** "because bit pi + 1 of every slot is 0".
* Line 165, "Let A be the sum of the extracted positions": **Fix:** "the sum of 2^e over the extracted positions e"
  (Proposition 9.4 already says this correctly).
* **Statement of Proposition 9.4 (line 114).** E(x) appears with b and pi unquantified, but the proof chooses them:
  2^pi > 2^{l+1}(r+1) and b = 2pi + l + 3, both depending on the representation of g. Theorem 9.5 says "there are
  b, pi". **Fix:** "for every N >= 1 there are b, pi and integers M, A >= 0 and distinct positions ...". The proof
  does not decide whether the forward direction holds for every fixed encoding. As weak, inconclusive evidence:
  a probe found no multiplier M < 2^17 that reads one step of Rule 110 from E(x)M with b = 3, pi = 1 or with
  b = 4, pi = 2, at N = 5 and 6.
* **Converse.** Multiplication then AND is case (Aff, Bit) of Proposition 9.2, which needs only N >= r. Correct.
  The case AND then multiplication is covered too.
* **Small N.** Nothing is missing. P handles wrap-around for N < r and N = 1, and the converse states N >= r. My
  test covers N = 1 to 10 for all 256 rules at k = 1, 2, 3 (r up to 7, so N < r occurs), and random tables with
  r = 1 to 5 and offsets o from -3 to r + 9 (o < 0 and o >= N included).
* The status line's count is right: 3 * 256 * (2 + 4 + ... + 2^10) = 1,571,328 rows. My own code checks exactly
  this set.

## 6. Closing paragraph (lines 179 to 184)

**Verdict: proved after a wording repair.**

* "three is the least number of operations ... among the programs of Proposition 9.2 and of three operations" is
  correct as far as it goes. Corollary 9.3 rules out two-operation programs of Proposition 9.2 for N >= 65
  (two steps) and N >= 119 (three steps). The program of Theorem 9.5 (multiply, AND, remainder, output at bit
  bj + pi) is a three-operation program in the same model for every N. But "least" also requires ruling out
  programs of one operation (or none), and the text does not mention them. They are ruled out: appending
  Y -> Y + 0 turns any shorter program into a two-operation program of an allowed shape (a lone remainder becomes
  "remainder, then + 0"). The sentence is also hard to parse ("and of three operations").
  **Proposed text:** "By Corollary 9.3, no program of at most two operations computes two steps of Rule 110 on a
  cyclic row of N >= 65 cells, or three steps on N >= 119 cells, unless it applies a remainder after a floor or a
  remainder (a shorter program followed by Y -> Y + 0 is a two-operation program). By Theorem 9.5, three
  operations suffice on every row. Two-operation programs that apply a remainder after a floor or a remainder
  are not covered."
* "Not covered" is accurate, and the last sentence about earlier claims is fine.
* For consistency outside Section 9: Introduction item (7) says "in a model of two-operation programs on long rows
  only BLF tables arise (Proposition 9.2)" without the exclusion. **Fix:** add "that do not apply a remainder after
  a floor or a remainder".

---

## Computations

Code in `/home/claude/coldread_s9/code/`:

* `common.py`: bits, elementary steps on cyclic rows, k-step tables composed on open windows, E(x).
* `blf_small.py`: BLF(3) by exhaustive search of bit j of K + a.x with 0 <= K, a_i < 2^{j+1}, j <= 3.
* `thm95.py`: M, A, D for Theorem 9.5, and M, A for Proposition 9.4, built exactly as the proof says. It checks
  against direct simulation, rebuilds the slots from the definition, and asserts the bounds and the spacing.
* `general_tables.py`: Theorem 9.5 for random tables, r = 1 to 5, and arbitrary offsets.
* `cor93.py`: window values, the square identity, and the N bounds.
* `lemma91.py`: the construction of Lemma 9.1, step by step, on random, clustered and bin-edge instances. It
  checks the conclusion, tests the literal reading of line 67, and builds the tightness example.
* `excluded_case.py`: floor after the lemma (always BLF), remainder after the lemma (not always BLF), and a stress
  test of the counting step.
* `fixed_encoding_probe.py`, `fixed_b_exact.py`: inconclusive probes of Proposition 9.4 with a fixed encoding.
  The exact single-cell test in `fixed_b_exact.py` shows that the obvious necessary condition can be met for
  Rule 110 at b = 2 to 6, so it gives no counterexample.

Outputs (from `code/outputs.txt`):

```
== blf_small.py
n=3, j<=2: 208 distinct BLF functions found
n=3, j<=3: 208 distinct BLF functions found
non-BLF elementary rules: 48
classes: 88  non-BLF classes: 15 [6, 9, 18, 27, 29, 33, 40, 46, 58, 72, 78, 130, 132, 172, 184]  mixed: []
Rule 110 BLF: True (2, 1, (1, 3, 3))

== thm95.py thm 8   (Theorem 9.5, all 256 rules, k = 1, 2, 3, every row, N <= 8, r = 3, 5, 7, o = k)
k=1: all 256 rules OK up to N=8
k=2: all 256 rules OK up to N=8
k=3: all 256 rules OK up to N=8
rows checked: 391680 (expected 391680 )
  k=1 N=1: L=2 pi=6 b=17 P=3 (blocks for rule 255: 9) M bits=1174
  k=2 N=1: L=3 pi=7 b=20 P=5 (blocks for rule 255: 33) M bits=7861
  k=3 N=1: L=3 pi=8 b=22 P=7 (blocks for rule 255: 129) M bits=45343
  k=3 N=8: L=3 pi=8 b=22 P=2 (blocks for rule 255: 129) M bits=90531

== thm95.py thm 10  (same, N <= 10)
k=1..3: all 256 rules OK up to N=10
rows checked: 1571328 (expected 1571328 )

== thm95.py prop 8  (Proposition 9.4 forward, 208 BLF rules, k = 1, every row, N <= 8,
                     4 representations (l, K, c) per rule; slot contents rebuilt and bounded for N <= 5)
BLF elementary rules: 208
Prop 9.4 forward: OK on 424320 (rule, representation, row) cases, N <= 8; max slot / 2^(2pi+ell+2) = 0.4632

== thm95.py big 12  (Rule 110 on 256 cells: all-zero row, single-one row, 10 random rows)
Rule 110, k=2, N=256: L=3 pi=7 b=20 P=2 blocks=18 bits: M=358441 A=358421 D=5120
  12 rows OK
Rule 110, k=3, N=256: L=3 pi=8 b=22 P=2 blocks=67 bits: M=1498179 A=1498157 D=5632
  12 rows OK

== general_tables.py
general tables: OK on 50800 rows (r = 1..5, 40 random tables each, random o in [-3, r+9], N <= 7)

== cor93.py
k=2: windows 00000..00011 -> values [0, 1, 1, 1]
k=2: windows 01000..01011 -> values [0, 1, 0, 0]
k=3: windows 0000000..0000011 -> values [0, 1, 1, 1]
k=3: windows 0010000..0010011 -> values [0, 1, 0, 0]
square identity checked on 149792 cases: OK
r=5: least N with floor(N/r) >= 2r+3 is 65 (claimed 65); 256 ok: True
r=7: least N with floor(N/r) >= 2r+3 is 119 (claimed 119); 256 ok: True

== lemma91.py
Lemma 9.1 construction: 8640 instances OK (r = 1..5, N from r(2r+3));
  case counts {'case1': 1546, 'case2': 7094, 'literal_exchange_fails': 399}
  counting step tight at m = 2r+2 (r=1..5): no good pair in star/triangle example: True

== excluded_case.py
(a) bit e of floor(Lambda/D) non-BLF cases (expected 0): 0
(b) clean example: Lambda = 1 + z0 + z1 + 2 z2, D = 5, bit 2 of Lambda mod 5: [0,0,0,1,0,1,0,0] = rule 40
    BLF: False | equals z2 AND (z0 XOR z1): True
(c) counting step: a good pair existed in all 18000 adversarial assignments at m = 2r+3, r = 1..6

== fixed_encoding_probe (inconclusive; M < 2^17, separate run)
rule 110, b=3, pi=1, N=5 and N=6: none;  rule 110, b=4, pi=2, N=5 and N=6: none
rule 160, b=3, pi=1, N=5: [97795, 98243];  other rule 160 cases at N = 5, 6: none
```

The Rule 110 table found for Proposition 9.4 is bit 2 of 1 + z_0 + 3 z_1 + 3 z_2, so l = 2 and Rule 110 is BLF,
in agreement with Corollary 5.3.

## Summary of proposed edits

1. Line 34: define the bitwise operations for Y < 0 (bit by bit, two's complement).
2. Line 67: replace "exchange the roles of V and V'" with the explicit second case (x_V' at the minimizer that
   defines I, x_V free, window V).
3. Line 88: replace "is handled as before" with the explicit statement at the cell whose window is V'.
4. Lines 103 to 104: say that the inputs are numbered 1 to r here, or shift the indices.
5. Line 114: "there are b, pi and integers M, A >= 0 ...".
6. Line 147: spell out the K term in the slot contents.
7. Line 165: "the sum of 2^e over the extracted positions e"; line 169: "bit pi + 1 of every slot is 0".
8. Lines 179 to 181: cover one-operation programs (padding with Y -> Y + 0), state the N bounds, and rephrase.
   Introduction item (7): mention the excluded case.
9. Optional: note that the proof of Proposition 9.2 allows any integer affine map and any bitwise constant, NOT
   included.

# Cold read of Sections 8 and 9 of the BLF preprint (23 Nov 2026)

Reader: an independent Claude Opus 5.5 agent that did not write the sections and was told not to read
the author's code. The agent could not write this file itself; its report was returned to the session
and is transcribed here. Its code and outputs are in `code/` (single thread, exact integers and
fractions, about 70 s in total).

## Verdicts

| Item | Verdict |
|---|---|
| Prop 8.1 (bit position upper bound) | proved (cosmetic: the case n = 1) |
| Lemma 8.2 (selector lemma) | proved |
| Lemma 8.3 (inverse entries to weights) | proved |
| Cor 8.5 and the Alon and Vu citations | proved after a wording repair (definition of chi(m)); citations accurate |
| Lemma 8.6 (seeds) | proved |
| Lemma 8.7 (Walsh lift) | proved after a wording repair (the spanning set of W) |
| Proof of Thm 8.4 | proved; exponent arithmetic checked exactly |
| Prop 9.1 and Cor 9.2 | proved after wording repairs (the constant a_0 clashed with cell x_0; name the fixed window when the floor is constant; cell numbering) |

All repairs were applied to the paper on 23 Nov 2026.

## Notes from the reader

- Alon and Vu, JCTA 1997: Theorem 2.1.1 is for orders 2^k; Theorem 3.3.1 gives the general lower bound
  with -n(2+o(1)); the paper states that no near optimal construction was known for other orders.
  Babai, Hansen, Podolskii and Sun (2010) still quote only the general -n(2+o(1)) bound. The reader did
  not search the literature after 2010 exhaustively.
- In Lemma 8.7 the bound |beta| <= 2 is attained (at l = 4, 5), so it cannot be improved in general.
- 1 - (8/15) log2(4/3) = 0.7786467 < 292/375 = 0.7786667; the margin is small but the integer inequality
  4^200 > 3^200 2^83 settles it.
- The status-only claims (exponent 5839/7500, the density-one exponent) are not part of any proof and
  were not checked.

## Computations

Seeds (Lemma 8.6): p = 3, 5, 7, 11, 13 pass: HH^T = dI, H normalized, DH^T lower triangular with
diagonal d (d/2 times), 4 (d/2 - 1 times), 2; |det D| = 2^(d-1).

Walsh lift (Lemma 8.7), built literally from the text; checks QQ^T = rI, L = AQ^T/r lower triangular
with the predicted diagonal, u_s = 4, doubling, det by Bareiss, (A^-1)_{0s} by exact elimination:

| p | l | r | s | abs(det A) | (A^-1)_{0s} | P/r | max abs(beta) |
|---|---|---|---|---|---|---|---|
| 3 | 3 | 64 | 56 | 2^63 | 1634780 | 16384 | 3/2 |
| 5 | 3 | 96 | 84 | 2^95 | 113515579023 | 127401984 | 4/3 |
| 7 | 3 | 128 | 112 | 2^127 | 19354866977513592 | about 2.2e12 | 5/4 |
| 3 | 4 | 128 | 88 | 2^127 | about 1.29e40 | about 6.5e31 | 2 |
| 5 | 4 | 192 | 132 | 2^191 | about 2.39e66 | about 7.6e53 | 2 |
| 3 | 5 | 256 | 128 | 2^255 | about 3.12e142 | about 5.8e119 | 2 |

Padding m = 64 to 66 and 70: abs(det) = 2^(m-1), same entry 1634780.

Selector lemma: 2, 4, 14, 104 threshold functions for m = 0..3 (124 in total), no mismatch with
ceil(log2(W1 + 1)). 0xfc80 = [x1 + 2x2 + 2x3 + 3x4 >= 5] has W1 = 8; z AND T is realized at bit 4 and
not at bit 3 (all 16^6 residue tuples searched).

Rule 110 squares on the last two inputs: 2 steps, windows 00000..00011 give 0,1,1,1 (needs equal
parities) and 01000..01011 give 0,1,0,0 (needs different parities); 3 steps, windows 0000000..0000011 and
0010000..0010011, the same patterns. So neither table is BLF.

The least j passing the test of Prop 8.1 for n = 1..12 is 2, 3, 4, 6, 7, 8, 10, 11, 13, 14, 16, 18
(sufficient only).

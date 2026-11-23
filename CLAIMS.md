# Claims, sources, review status and certification

Every result planned for the BLF preprint (Joseph S. Farland, 2026), where it came from, how it was
checked, and which Lean theorems certify it. Paper numbering will be added when the preprint is
final. Record numbers (R-...) are those of the project's research ledger; seat names are Claude
agents (Anthropic) run by the author.

Labels: **Lean** = kernel-checked theorem in this repository, standard axioms only, no `sorry`, no
`native_decide`. Which commit and statements each independent Lean audit covered is in `review/README.md`. **Computer** = exhaustive computation with the code in `compute/`, reproduced by an
independent reader's own code. **Paper** = proof in `proofs/`, read by an independent cold reader.

| Result | Statement (short) | Source | Review | Certification |
|---|---|---|---|---|
| Parallelogram inequality | floors of (K + a.x)/2^j: second differences over x + y = z + w lie in {-1, 0, 1}, every n | Claude Opus 5.5 (21 Nov) | Lean | Lean: `BLF.floor_parallelogram` |
| Closure | BLF is closed under XOR with GF(2)-affine functions, every n | seat BL-O (R-096) | Lean | Lean: `BLF.isBLF_xor_affB` |
| Thresholds | every threshold function is BLF, every n | seat BL-O (R-096) | Lean, cold reader | Lean: `BLF.threshold_isBLF` |
| Counts n <= 4 | 4, 16, 208, 10368 | n = 3: BL-O; n = 4: ChatGPT A2, checked (R-096) | Lean, brute force by two readers | Lean: `BLF.blf_count_one` to `BLF.blf_count_four` |
| Characterization | f is BLF iff f = floor(u) mod 2 for a real affine u, every n | seat BL-O (R-096) | cold reader (proofs/PROOF_R096.md, coldread/R096) | Paper |
| n = 3 equality, n = 4 decomposition | BLF(3) = threshold XOR affine; BLF(4) = threshold XOR affine together with the translates of bit 1 of x1 + x2 + x3 + x4 | BL-O; ChatGPT A2, checked | Lean, cold reader with own code | Lean: `BLF.blf_three_iff_threshold_xor_affine`, `BLF.blf_four_iff` |
| n = 4 boundary is strict | bit 1 of x1 + x2 + x3 + x4 is BLF and not threshold XOR affine, so exactly 32 functions of BLF(4) are not threshold XOR affine | BL-O; ChatGPT A2, checked; Lean proof written by the second verifier seat after its report | no independent audit of the Lean statement (added at 9e48384, after both reports; see review/README.md); mechanical: CI comparator, three kernels; the 32 extra functions recounted by review/lean2's own code | Lean: `BLF.bitOneSum_isBLF_not_txa` (with `BLF.blf_four_iff`) |
| n = 5 structure | 3,750 extra classes in 15 orbits | ChatGPT Q13, checked | cold reader with own code | Computer (thresh.c, twbound.c, maxminor.c) |
| Cellular automata | 73 of the 88 elementary CA classes are BLF; the 15 others listed | seat BL-O (R-096) | cold reader | Computer (ca_classes.py) |
| Counts n = 5, 6 | 1903808 and 1359244544 | ChatGPT (n = 5), seat BL6-O (n = 6) (R-107) | rebuilt 21 Nov: universal grid (n = 5), three independent routes for R_6 | Computer |
| Toric identity | |BLF(n)| = 2^n (R_n + 1), every n | seat TB-O from a ChatGPT lead (R-116); proof rebuilt 21 Nov | cold reader (proofs/PROOF_R116.md, coldread/R116) | Paper |
| Asymptotics | log2 |BLF(n)| = n^2 - (1/2) n log2 n + O(n) | TB-O (upper), ChatGPT A22 (lower) (R-116) | two cold reads | Paper |
| Bit position, upper bound | every BLF function of n variables is bit j of a linear form once 2^(2j+2n+2) > (n+1)^2 (n+2)^(n+2); j*(n) = n - 1 for n <= 6 | universal grid (Claude, 21 Nov); doubling step from ChatGPT Q15 round 1 | cold read (coldread/S89) | Paper; Computer for n <= 6 |
| Selector lemma | least bit of z AND T(x) is ceil(log2(W1(T) + 1)), W1 = least l1 weight of T | ChatGPT Q15 round 1 (part C), audited by a separate review | cold read (coldread/S89); brute force for all thresholds with n <= 3 and for 0xfc80 (compute/selector.py) | Paper |
| Inverse entries to weights | a nonsingular sign matrix A gives a threshold T with W1(T) >= sum_i abs((A^-1)_ci) | Alon and Vu, Section 3.3; explicit ties from ChatGPT Q15 rounds 2 and 3 | cold read (coldread/S89) | Paper |
| Anti-Hadamard matrices of every large order (R-114) | sign matrices of every large order m with abs(det) = 2^(m-1) and an inverse entry 2^((1/2) m log2 m - m - O(m^(292/375))) | ChatGPT Q15 rounds 2 to 4, each audited by a separate review; earlier write-up by seat AH-O lost | cold read (coldread/S89); checkers of the answers rerun; independent implementation (compute/antihadamard.py) at orders 64 to 448 | Paper |
| Bit position, asymptotic | j*(n) = (1/2) n log2 n - n + O(n^(292/375)) | from the four rows above | cold read (coldread/S89) | Paper |
| One-step cellular automata | a local table computed at every cell of a cyclic row with floor(N/r) >= 2r + 3 by one multiplication, one division or remainder and a bit readout is BLF; two and three steps of Rule 110 are not BLF | ChatGPT Q15 round 1 (part A), audited by a separate review | cold read (coldread/S89); square patterns checked (compute/selector.py) | Paper |
| Parallelogram characterization, n <= 6 | integer G on the cube is a normalized floor vector iff all parallelogram second differences are in {-1, 0, 1} | Claude Opus 5.5 (21 Nov) | computed | Computer (parallelogram.c), observation |

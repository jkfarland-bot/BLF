# Independent verification of the BLF Lean formalization (lean3)

- Verifier: Claude (Opus 5.5), independent verifier subagent; did not write the code under audit.
- Date: 2026-11-23.
- Commit audited: `a5d08eef2b766635b2608db600bf67de26227a2e` (a5d08ee) of `/home/claude/blf`, cloned to
  `/home/claude/verify_lean3` and checked out there; nothing in `/home/claude/blf` was modified.
- Toolchain: Lean and Lake `v4.35.0-rc2` (Lean commit 11acb17), Mathlib `v4.35.0-rc2`.
- Statements covered (all sixteen in `Challenge.lean` and `comparator.json`):
  1. `BLF.floor_parallelogram`
  2. `BLF.threshold_isBLF`
  3. `BLF.isBLF_xor_affB`
  4. `BLF.blf_count_one`
  5. `BLF.blf_count_two`
  6. `BLF.blf_count_three`
  7. `BLF.blf_count_four`
  8. `BLF.blf_three_iff_threshold_xor_affine`
  9. `BLF.blf_four_iff`
  10. `BLF.bitOneSum_isBLF_not_txa`
  11. `BLF.isBLF_iff_floor` (new)
  12. `BLF.selector_iff` (new)
  13. `BLF.gated_threshold_bit_four` (new)
  14. `BLF.blf_five_needs_bit_four` (new)
  15. `BLF.rule110Two_not_isBLF` (new)
  16. `BLF.rule110Three_not_isBLF` (new)
- Verifier files: Lean scratch files in `/home/claude/verify_lean3/Verify/` (`Axioms.lean`,
  `AxiomsControl.lean`, `ChallengeList.lean`, `EvalDefs.lean`, `NonVacuity.lean`); scripts and logs in
  `/home/claude/vscratch3/` (`indep.py`, `txa_check.py`, `residues.c`, `planted.sh`,
  `planted_predict*.py`, `memsample.sh`, `*.log`, `*.out`).

## Summary (one line per check)

1. Fresh `lake build` (no `.lake/build`, Mathlib packages reused): exit 0, 8964 jobs, 3 min 39 s; 29 warnings = 16 expected `declaration uses sorry` (Challenge.lean only) + 13 linter notes (9 unused simp arguments, 4 `<;>` style); no errors.
2. Source hygiene: `sorry` only in Challenge.lean (16 proofs + 1 docstring mention); no native_decide, axiom, implemented_by, extern, unsafe, opaque, csimp, run_cmd, #eval, elab, macro, syntax, attribute or debug options; found only `noncomputable def ulin` (Char.lean), one `Decidable` instance for `sqOk` (Square.lean) and `set_option maxHeartbeats 4000000` (TxaData3/4), all harmless; `check-lean-sources.py` exit 0; definition blocks byte identical (`cmp` exit 0, 2184 bytes, same SHA-256).
3. Axioms: `Lean.collectAxioms` over all 443 `BLF.*` constants (334 theorems) of BLF + Solution finds only `propext`, `Classical.choice`, `Quot.sound` (0 offending); `#print axioms` on the sixteen headline theorems gives exactly those three; control on Challenge flags all 16 headline statements with `sorryAx`.
4. Statement audit: all sixteen statements say what their docstrings say; `bitAt` is floor division (checked by evaluation), `eca` is Wolfram numbering (rules 30, 90, 110 checked), and the Lean truth tables of `rule110Two` (32 rows) and `rule110Three` (128 rows) equal the verifier's Python Rule 110, kernel-checked by `decide`.
5. Non-vacuity: `Verify/NonVacuity.lean` compiles (no errors, no sorry): XOR and majority-of-3 (real parameters 1/3) are BLF via `isBLF_iff_floor`; one step of Rule 110 is BLF (`j = 2, K = -7, a = (-7, -5, -5)`); `selector_iff` used in both directions (bit-1 and bit-4 instances; `z AND (x0 xor x1)` is not bit `j` for any `j`; `z AND x0` is not bit 0); a non-BLF function of 3 and of 4 variables exists by the counts.
6. Independent recount: my own exact BLF test (edge parities + LP) and my own residue enumeration (C) both give |BLF(n)| = 4, 16, 208, 10368 for n = 1..4; TXA(3) = BLF(3) and TXA(4) plus bit-1 translates = BLF(4) (10336 + 32); 0xfc80 gated function: least weight sum 8, realizable at bit 4, not at bits 0..3; Rule 110 two and three steps fail the square condition for every parity vector (not BLF), one step is BLF.
7. Planted errors: all 7 rejected (P1 rule 111 in `rule110Two`: Rule110.lean fails; P2 Challenge-only 111: cmp fails; P3 `<` to `<=` in selector_iff: Solution type mismatch; P4 `bitAt 4` to `bitAt 3`: Solution type mismatch; P5 witness 3 to 2 in Gated.lean: decide fails; P6 one docstring byte: cmp fails; P7 `4 * l` to `5 * l` in Challenge's `eca`: cmp fails and the comparator reports "Const does not match between challenge and target 'BLF.eca'"); tree restored to a5d08ee after each.
8. Comparator (`./scripts/verify-comparator.sh`): "con-ron: accepted 15803 declarations (--verified)", "con-ron kernel accepts the solution", "nanoda kernel accepts the solution", "Lean default kernel accepts the solution", "Your solution is okay!"; exit 0, 5 min 54 s wall; peak RSS 4.73 GB (con-ron), 4.88 GB summed over judge processes.

## 1. Fresh build

Setup: `git clone /home/claude/blf /home/claude/verify_lean3 && git checkout a5d08ee`; no `.lake/build`
existed in the copy. `.lake/packages` was first a symlink to `/home/claude/blf/.lake/packages` (only 3.6 GB
of disk was free, the packages take 7.5 GB). The build ran on that. For the comparator (check 8) the symlink
was replaced by a hardlinked tree (`cp -al`, same filesystem, no extra data blocks), because the comparator's
bubblewrap sandbox mounts only the project directory and the symlink dangles inside it; `lake build
--no-build` confirmed afterwards that all targets were still up to date.

`lake build`: exit 0, "Build completed successfully (8964 jobs)", 3 min 39 s wall. Warnings (29):

- 16 x `declaration uses sorry`, at Challenge.lean lines 82, 88, 93, 98, 102, 107, 111, 115, 120, 127, 134,
  141, 149, 159, 165, 169 (the sixteen statements; by design).
- 9 x unused simp argument: BLF/Square.lean:48 (`h3.1`), BLF/Selector.lean:206 (`min_le_left`,
  `min_le_right`), 208 (`le_max_left`, `le_max_right`), BLF/Small.lean:54 and 59
  (`Function.update_of_ne hk`), BLF/TxaData3.lean:35 (`List.all_append`, `Bool.and_self`).
- 4 x `tac1 <;> tac2 where (tac1; tac2) would suffice`: BLF/Selector.lean:129 and 130, BLF/Floor.lean:60,
  BLF/Txa.lean:25.

No warning outside Challenge.lean mentions `sorry`. Peak memory: largest single process 4.24 GB (a `lean`
worker); the summed RSS of all Lean and Lake processes peaked at 7.15 GB, which double counts shared
memory-mapped `.olean` pages; no process was killed in the 6 GiB cgroup.

## 2. Source hygiene

Searched all 31 tracked `.lean` files (`git grep`, word boundaries) for `sorry`, `native_decide`, `axiom`,
`implemented_by`, `extern`, `unsafe`, `opaque`, `csimp`, `run_cmd`, `run_tac`, `#eval`, `elab`, `macro`,
`macro_rules`, `syntax`, `instance`, `attribute`, `set_option`, `partial`, `noncomputable`, `private`,
`local`, `scoped`, `export`, `ofReduceBool`, `trustCompiler`, `debug`, `#exit`, `import Lean`, and any `@[...]`
other than the module's `@[expose] public section`.

- `sorry`: only Challenge.lean (16 lines consisting of `  sorry`, plus the word in the module docstring).
- `noncomputable def ulin` (BLF/Char.lean:21): a real-valued helper `t + r.x`; not used in any statement.
  Harmless.
- `instance ... : Decidable (sqOk βi βk f00 f01 f10 f11) := by unfold sqOk; infer_instance`
  (BLF/Square.lean:27): a `Decidable` instance for an equation of natural numbers, derived from Lean's own
  `Nat` decidable equality. Every `Decidable` value carries its proof (`isTrue h` or `isFalse h`), so no
  instance can make `decide` prove something false; it is used only by the `decide +kernel` steps in
  BLF/Rule110.lean, and `sqOk` does not occur in any statement. Harmless.
- `set_option maxHeartbeats 4000000` (BLF/TxaData3.lean:10, BLF/TxaData4.lean:10): a resource limit only.
  Harmless.
- `decide` is used 80 times and `decide +kernel` 152 times; no `native_decide` and no `+native`. The axiom
  collector (check 3) confirms no `Lean.ofReduceBool`.
- No attribute declarations, no `#` commands, no imports beyond `Mathlib` and the project's own modules.
- `python3 scripts/check-lean-sources.py`: exit 0 (run on the clone before the scratch files were added, and
  again on a pristine `git archive a5d08ee` export: exit 0). Note: this script checks module headers, UTF-8,
  symlinks and the 10,000 line cap only; the keyword scan above is the verifier's own.
- Byte identity: the CI command
  `cmp <(sed -n '/^-- BEGIN STATEMENT DEFINITIONS/,/^-- END STATEMENT DEFINITIONS/p' Challenge.lean) <(sed ... BLF/Defs.lean)`
  exits 0; both blocks are 2184 bytes with SHA-256 `335a3d89...42726`.
- `comparator.json` lists exactly the sixteen Challenge theorem names in file order, the Solution has the
  same sixteen names in the same order, `definition_names` is empty and the permitted axioms are `propext`,
  `Quot.sound`, `Classical.choice`.

## 3. Axioms

`Verify/Axioms.lean` imports `Lean`, `BLF` and `Solution` and runs `Lean.collectAxioms` on every constant
whose name has prefix `BLF` (definitions, theorems and auxiliary constants):

```
BLF constants checked: 443 (theorems: 334); axioms used overall: [Quot.sound, Classical.choice, propext];
offending: 0 []
```

`#print axioms` for each of the sixteen headline theorems prints
`depends on axioms: [propext, Classical.choice, Quot.sound]` (all sixteen identical).

Control, `Verify/AxiomsControl.lean` (imports `Challenge` instead): the same collector flags 16 of the 18
`BLF.*` theorems there as using a non-permitted axiom, and `#print axioms BLF.rule110Two_not_isBLF` and
`BLF.selector_iff` show `sorryAx`. The two unflagged ones are the compiler-generated side proofs
`BLF.rule110Two._proof_1 : NeZero (4 + 1)` and `BLF.rule110Three._proof_1 : NeZero (6 + 1)` from the `Fin`
literals in the definitions (`Verify/ChallengeList.lean`).

## 4. Statement audit (all sixteen)

Definitions (block shared by Challenge.lean and BLF/Defs.lean):

- `bval b = if b then 1 else 0 : ℤ`; `lin K a x = K + ∑ i, a i * bval (x i)`: as documented.
- `bitAt j N = decide (N / 2 ^ j % 2 = 1)` on `ℤ`: `/` and `%` are `Int.ediv`/`Int.emod`; for the positive
  divisor `2^j` this is floor division and the remainder is in {0, 1}. Evaluated: `bitAt 0 (-1)`,
  `bitAt 5 (-1)` true, `bitAt 1 (-3)` false, `bitAt 0 (-3)` and `bitAt 2 (-3)` true (two's complement of
  -3 is ...11101), `(-7)/4 = -2`, `(-7)%4 = 1`. BLF/Char.lean also proves `⌊(N:ℝ)/2^j⌋ = N / 2^j`.
- `IsBLF f = ∃ j K a, ∀ x, f x = bitAt j (lin K a x)`: no bound on `j`, free constant, integer coefficients.
- `affB c b x = decide ((bval c + ∑ bval (b i) * bval (x i)) % 2 = 1)`: GF(2)-affine.
- `IsTXA f = ∃ w0 w c b, ∀ x, f x = xor [0 < w0 + w.x] (affB c b x)`.
- `eca R l c r = R.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)`: Wolfram numbering. Evaluated for 110 on
  the patterns 111..000: `0,1,1,0,1,1,1,0` = 01101110 = 110; for rule 30 the table reads 00011110 and for
  rule 90 01011010, as they should.
- `rule110Two x = eca 110 (eca 110 x0 x1 x2) (eca 110 x1 x2 x3) (eca 110 x2 x3 x4)`: two steps on a 5-cell
  window, `x 0` leftmost (passed as the left neighbour). `rule110Three` applies `rule110Two` to the five
  one-step cells of a 7-cell window. Kernel-checked (`decide +kernel` in `Verify/EvalDefs.lean`) that the
  Lean truth tables, indexed by `v = ∑ x_i 2^i`, equal the verifier's Python tables built from the literal
  Rule 110 table: `rule110Two` = `00001111110000111111000111001100`, `rule110Three` = the 128-character
  string in `vscratch3/r110_tt_python.txt`. Orientation spot check: a single live cell at `x 4` reaches the
  centre after two steps, one at `x 0` does not (Rule 110 grows to the left).

Statements:

1. `floor_parallelogram`: for all `n, j, K, a` and vertices with `bval x_i + bval y_i = bval z_i + bval w_i`
   for every `i`, `|F x + F y - F z - F w| <= 1` with `F = lin K a / 2^j` (floor). Matches the docstring.
2. `threshold_isBLF`: `[0 < w0 + w.x]` is BLF for all `n`. Matches.
3. `isBLF_xor_affB`: `IsBLF f -> IsBLF (f xor affB c b)` for all `n`. Matches.
4. to 7. `blf_count_*`: `Nat.card {f // IsBLF f}` = 4, 16, 208, 10368 for n = 1..4. The subtype is finite, so
   `Nat.card` is its cardinality (not the 0 of an infinite type). Matches; recounted in check 6.
8. `blf_three_iff_threshold_xor_affine`: `IsBLF f <-> IsTXA f` for n = 3. Matches.
9. `blf_four_iff`: for n = 4, `IsBLF f <-> IsTXA f or f = bit 1 of (x1+x2+x3+x4) xor affine`. Matches.
10. `bitOneSum_isBLF_not_txa`: bit 1 of `x1+...+x4` is BLF and not TXA. Matches.
11. `isBLF_iff_floor`: `IsBLF f <-> ∃ t : ℝ, ∃ r : Fin n -> ℝ, ∀ x, f x = decide (⌊t + ∑ r i * bval (x i)⌋ % 2 = 1)`,
    with `Int.floor` of a real affine form and integer parity. Matches Proposition 2.1 as described.
12. `selector_iff`: for all `n`, `j`, `T`:
    `(∃ K c a, ∀ x z, (z && T x) = bitAt j (lin K a x + c * bval z)) <-> ∃ w τ, ∑ |w i| < 2^j ∧ ∀ x, T x = decide (τ <= w.x)`.
    This is exactly "z AND T is bit j of an integer affine form in (x, z) iff T = [τ <= w.x] with
    sum |w_i| < 2^j", with integer `w`, `τ`, `K`, `c`, `a`. The bound is strict (planted `<=` is rejected,
    check 7), and the `j = 0` case correctly forces constant `T` (check 5).
13. `gated_threshold_bit_four`: with `x 0..x 3` as `x1..x4`, `z AND [5 <= x1 + 2x2 + 2x3 + 3x4]` is bit 4 of
    some `K + a.x + c z` and is not bit 3 of any such form. The threshold is written out in the statement
    (no auxiliary definition). Matches.
14. `blf_five_needs_bit_four`: `∃ f` of 5 variables, `IsBLF f` and for every `j <= 3` no `K, a` gives
    `f = bit j of K + a.x`. Since the sets of functions realizable at bit `j` increase with `j`, this is
    equivalent to "no `j <= 3` serves all of BLF(5)", i.e. `j*(5) >= 4`. It does not claim `j*(5) = 4`, nor
    does the docstring.
15. `rule110Two_not_isBLF`: `¬ IsBLF rule110Two`. Matches (definition checked above).
16. `rule110Three_not_isBLF`: `¬ IsBLF rule110Three`. Matches.

## 5. Non-vacuity (`Verify/NonVacuity.lean`, compiles with no errors, warnings or sorry)

- `IsBLF (x0 xor x1)` from `isBLF_iff_floor` with `t = 0`, `r = (1, 1)`.
- `IsBLF (majority of 3)` from `isBLF_iff_floor` with the non-dyadic reals `t = 1/3`, `r = (1/3, 1/3, 1/3)`.
- Forward direction: a real representation of one Rule 110 step obtained from its integer witness.
- One step of Rule 110 is BLF: `⟨2, -7, ![-7, -5, -5], by decide +kernel⟩`; also as a 5-variable function on
  the middle cells (`![0, -7, -5, -5, 0]`). So `rule110Two_not_isBLF` is not a statement about every function.
- `selector_iff`, right to left: `T = x0` with `w = (1)`, `τ = 1` at `j = 1`; the Section 8 threshold with
  `w = (1, 2, 2, 3)`, `τ = 5` at `j = 4`.
- `selector_iff`, left to right: for every `j`, `z AND (x0 xor x1)` is not bit `j` of any integer form in
  `(x, z)`; `z AND x0` is not bit 0 (the bound `∑|w| < 1` forces `w = 0`), while it is bit 1 of `x0 + z`.
- `∃ f : (Fin 3 -> Bool) -> Bool, ¬ IsBLF f` and the same for 4 variables, from `blf_count_three`/`four`.
- `∃ f, IsBLF f ∧ f ≠ rule110Two`, combining `blf_five_needs_bit_four` and `rule110Two_not_isBLF`.

## 6. Independent recount (verifier's own code)

- Exact BLF test (`vscratch3/indep.py`, derived independently from the floor characterization): f is BLF iff
  for some parity vector `β` the edge rises `D_l(x) = f(x) xor f(x+e_l) xor β_l` are path independent and the
  resulting integer function is the floor of a real affine function (LP with a positive margin, scipy HiGHS).
  Counts: |BLF(1)| = 4, |BLF(2)| = 16, |BLF(3)| = 208 (all functions tested), |BLF(4)| = 10368 (one test per
  affine-XOR orbit; orbits are free of size 32). No near-zero margins were reported.
- Residue enumeration (`vscratch3/residues.c`): bit `j` of `N` depends on `N mod 2^(j+1)`, so `K, a_i` range
  over residues. Union over `j <= 0..4`: n=1: 4,4,4,4,4; n=2: 8,16,16,16,16; n=3: 16,80,208,208,208;
  n=4: 32,384,5248,10368,10368.
- TXA check (`vscratch3/txa_check.py`): threshold counts 4, 14, 104, 1882 for n = 1..4 (the known values);
  TXA(3) = BLF(3) (208); |TXA(4)| = 10336, and TXA(4) together with the 32 affine translates of bit 1 of
  `x1+x2+x3+x4` is exactly my BLF(4) (10368); bit 1 of the sum is BLF and not TXA.
- 0xfc80: the truth table of `[x1 + 2x2 + 2x3 + 3x4 >= 5]` is mask 0xfc80; the least `∑|w_i|` of an integer
  representation `[τ <= w.x]` is 8 (search over `[-8, 8]^4`), so bit 3 (needs `<= 7`) is impossible and bit 4
  possible. Direct residue search for `z AND T` as a 5-variable function (mask 0xfc800000): not realizable at
  bits 0, 1, 2, 3; realizable at bit 4. The Lean witness `7 + x1 + 2x2 + 2x3 + 3x4 + 4z`, bit 4, is correct on
  all 32 inputs. My exact test says the gated function is BLF.
- Rule 110: one step is BLF; for two steps (5 cells) and three steps (7 cells) the square condition fails for
  every `β` (so neither is BLF). The two squares used in BLF/Rule110.lean (directions 3, 4 at `p = 0` and
  `p = e1`; directions 5, 6 at `p = 0` and `p = e2`) are jointly unsatisfiable for all four `(βi, βk)`,
  which is what the `decide +kernel` steps check.

## 7. Planted errors (`vscratch3/planted.sh`, each restored with `git checkout`)

| id | change | expected | result |
|----|--------|----------|--------|
| P1 | outer `eca 110` to `eca 111` in `rule110Two`, in Challenge.lean and BLF/Defs.lean (cmp still 0) | proof fails | `BLF/Rule110.lean:23:2: Tactic decide proved that the proposition ... is false`, build exit 1 |
| P2 | same change in Challenge.lean only | cmp fails | cmp exit 1 |
| P3 | weight bound `< 2 ^ j` to `<= 2 ^ j` in `selector_iff`, Challenge.lean and Solution.lean | Solution fails | `Solution.lean:88:2: Type mismatch`, exit 1 |
| P4 | `bitAt 4` to `bitAt 3` in `gated_threshold_bit_four`, Challenge.lean and Solution.lean | Solution fails | `Solution.lean:99:9: Application type mismatch`, exit 1 |
| P5 | witness `![1, 2, 2, 3]` to `![1, 2, 2, 2]` in `tFC80_bit_four` (BLF/Gated.lean) | proof fails | `BLF/Gated.lean:25:41: Tactic decide proved that the proposition ... is false`, exit 1 |
| P6 | one docstring byte in BLF/Defs.lean (`integer` to `Integer`) | cmp fails | cmp exit 1 |
| P7 | `4 * l.toNat` to `5 * l.toNat` in Challenge.lean's `eca` only | cmp fails; comparator fails | cmp exit 1; comparator exit 1 with `Const does not match between challenge and target 'BLF.eca'` |

My Python predicted P1 before the run: with the outer rule changed to 111 the function is still not BLF, but
the two specific squares used in the proof become jointly satisfiable, so the proof had to fail. After the
last restore `git diff a5d08ee` is empty and `lake build` completed successfully again (from Lake's artifact
cache).

## 8. Comparator

`./scripts/verify-comparator.sh` (bubblewrap at `/usr/bin/bwrap`; toolchain-bundled kernels):

```
Running con-ron kernel on solution
con-ron: accepted 15803 declarations (--verified)
con-ron kernel accepts the solution
Running nanoda kernel on solution
nanoda kernel accepts the solution
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```

Exit 0, 5 min 54 s wall. The export lists all sixteen theorem names. Peak memory (RSS sampled every 0.5 s):
con-ron 4.73 GB (the largest single process), 4.88 GB summed over all judge processes; within the 6 GiB
cgroup. The first attempt, with `.lake/packages` as a symlink pointing outside the project, failed before
judging (`mathlib: materializing new dependency ... already exists`) because the sandbox does not see the
symlink target; this is an artefact of the verifier's setup, not of the repository.

## Issues and suggestions

No correctness issue found. Minor points:

1. 13 linter warnings (unused simp arguments and `<;>` style, listed in check 1). Cosmetic; removing the
   named simp arguments and replacing the four `<;>` by `;` would make the build warning-free outside
   Challenge.lean.
2. `scripts/check-lean-sources.py` does not scan for forbidden keywords (`native_decide`, `axiom`, ...); the
   axiom check is left to the comparator. Optional: add a `git grep` step to CI, mirroring check 2.
3. For future verifiers working from a copy: give the copy a real or hardlinked `.lake/packages`
   (`cp -al` on the same filesystem); a symlink outside the project breaks `lake comparator`'s sandbox.

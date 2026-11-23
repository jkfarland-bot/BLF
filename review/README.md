# Review record: what each report covers

| Report | Commit audited | Statements audited | Checks | Comparator |
|---|---|---|---|---|
| `lean3/VERIFY_LEAN3.md` (23 Nov 2026) | `a5d08ee` | all 16 in `Challenge.lean`: `floor_parallelogram`, `threshold_isBLF`, `isBLF_xor_affB`, `blf_count_one` to `blf_count_four`, `blf_three_iff_threshold_xor_affine`, `blf_four_iff`, `bitOneSum_isBLF_not_txa`, `isBLF_iff_floor`, `selector_iff`, `gated_threshold_bit_four`, `blf_five_needs_bit_four`, `rule110Two_not_isBLF`, `rule110Three_not_isBLF` | fresh rebuild, source hygiene, byte identity of the definitions, axiom collector over all 334 theorems, statement audit (including `eca`, `rule110Two` and `rule110Three` against an independent Python Rule 110), non-vacuity instances, own recount for n <= 4 and of the new examples, seven planted errors | Lean kernel, nanoda and con-ron accepted all sixteen |
| `lean2/VERIFY_LEAN2.md` (21 Nov 2026) | `3e2e68f` | 9: the first seven above and `blf_three_iff_threshold_xor_affine`, `blf_four_iff` | the same kinds of checks on those nine | Lean kernel, nanoda and con-ron accepted all nine |
| `lean1/VERIFY_LEAN.md` (21 Nov 2026) | `cb688a7` | 7: `floor_parallelogram` to `blf_count_four` | the same kinds of checks on those seven | partial: Lean kernel and con-ron accepted; nanoda ran out of memory on `blf_count_four` (6 GiB sandbox) |

All three verifiers were Claude Opus agents (Anthropic) that did not write the code they checked.

**Coverage of the current submission.** The third report audits commit `a5d08ee`, which states all
sixteen theorems. The Lean sources (`*.lean`, `comparator.json`, `lakefile.toml`, `lean-toolchain`,
`lake-manifest.json`) have not changed since `a5d08ee`; later commits change documentation, metadata
and the programs in `compute/` only. The first two reports concern earlier commits and are kept for the
record. The proof of `bitOneSum_isBLF_not_txa` (`BLF/Strict.lean`) was written by the second verifier after
it filed its report; the third report audits that statement and its proof.

**Mechanical verification.** Separately from these audits, on every push GitHub Actions
(`.github/workflows/build.yml`) builds the project, checks the Lean source requirements and the byte
identity of the definitions block, validates `formalization.yaml`, and runs the toolchain's
`lake comparator` (`scripts/verify-comparator.sh`), which accepts the theorems with the Lean kernel, nanoda
and con-ron and permits only `propext`, `Quot.sound` and `Classical.choice`.

No human referee has reviewed the formalization.

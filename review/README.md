# Review record: what each report covers

| Report | Commit audited | Statements audited | Checks | Comparator |
|---|---|---|---|---|
| `lean1/VERIFY_LEAN.md` (21 Nov 2026) | `cb688a7` | 7: `floor_parallelogram`, `threshold_isBLF`, `isBLF_xor_affB`, `blf_count_one`, `blf_count_two`, `blf_count_three`, `blf_count_four` | fresh rebuild, source hygiene, byte identity of the definitions, axiom collector over all theorems, statement audit, non-vacuity, own recount for n <= 4, planted errors | partial: Lean kernel and con-ron accepted; nanoda ran out of memory on `blf_count_four` (6 GiB sandbox) |
| `lean2/VERIFY_LEAN2.md` (21 Nov 2026) | `3e2e68f` | 9: the seven above (textually unchanged since `cb688a7`, checked by diff), `blf_three_iff_threshold_xor_affine`, `blf_four_iff` | the same checks on those nine | Lean kernel, nanoda and con-ron accepted all nine |

Both verifiers were Claude Opus agents (Anthropic) that did not write the code they checked.

**Not covered by either report.** The tenth statement, `bitOneSum_isBLF_not_txa`, and its proof
`BLF/Strict.lean` were added at commit `9e48384`, after both reports. The proof was written by the
second verifier agent after it filed its report, from its non-vacuity lemma (`lean2/NonVacuity2.lean.txt`).
No independent report audits this statement. From `3e2e68f` to `9e48384` the Lean sources changed only
by that statement (`Challenge.lean`, `Solution.lean`), its proof (`BLF/Strict.lean`), its entry in
`comparator.json` and the import in `BLF.lean`. The Lean sources have not changed since `9e48384`.

**Mechanical verification of the current submission.** The ten-theorem submission is checked
mechanically, which is separate from the audits above: on every push, GitHub Actions
(`.github/workflows/build.yml`) builds the project, checks the Lean source requirements and the byte
identity of the definitions block, validates `formalization.yaml`, and runs the toolchain's
`lake comparator` (`scripts/verify-comparator.sh`). It accepts all ten theorems with the Lean kernel,
nanoda and con-ron, and permits only `propext`, `Quot.sound` and `Classical.choice`. An example is the
run on commit `3d90ee7` (23 Nov 2026).

No human referee has reviewed the formalization.

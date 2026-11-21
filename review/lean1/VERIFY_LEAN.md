# Independent verification of the BLF Lean formalization

Verifier: independent Claude agent (did not write the code), 2026-11-21.
Object verified: a copy of /home/claude/blf at commit cb688a768e84f00b9673272575f6096e3cc397fd
(clean working tree in the copy at /home/claude/verify_lean). Toolchain leanprover/lean4:v4.35.0-rc2,
Mathlib v4.35.0-rc2. Machine: 7 GB RAM, but this shell runs in a 6 GiB memory cgroup.
Nothing under /home/claude/blf was modified. Verifier files are in /home/claude/verify_lean/Verify/
and /home/claude/vscratch/.

Important scope note: while this check ran, /home/claude/blf gained uncommitted work in progress
(modified BLF.lean, BLF/Defs.lean, Challenge.lean, Solution.lean, comparator.json; new BLF/Txa*.lean,
scripts/gen_txa.py; a new definition IsTXA and two new theorems blf_three_iff_threshold_xor_affine and
blf_four_iff). None of that is covered by this report. The remote origin is also at a different
commit (376a3e7), and no GitHub Actions runs exist for the repository.

## Results, one line per check

1. Fresh rebuild: PASS. `lake build` (default targets BLF, Challenge, Solution) on the copy with
   .lake/build removed: 8953 jobs, exit 0, 3 min 58 s wall (Mathlib replayed from cache; Check4 74 s,
   Data4 54 s, Small4 31 s). Warnings: 7 x "declaration uses sorry" in Challenge.lean only (expected);
   otherwise only style or deprecation lints (push_neg deprecated in Basic.lean:38 and Small.lean:45,
   unused simp args Small.lean:54,59, if_true deprecated Small.lean:135,155,172, unnecessary <;>
   Floor.lean:60). None affect soundness.
2. Source hygiene: PASS. Grep of all files outside .lake and .git: `sorry` occurs in Lean code only in
   Challenge.lean (7, one per stated theorem); other hits are prose in README.md, CLAIMS.md,
   formalization.yaml, scripts. No native_decide, no `axiom`, no `set_option debug`, no implemented_by,
   no unsafe, no opaque in any .lean file (`extern` appears only in C comments in compute/nbc.c and the
   string external_kernels in scripts/verify-comparator.sh). Also no csimp, macro, elab, run_cmd, #eval,
   instance or attribute declarations in BLF/ or Solution.lean. scripts/check-lean-sources.py exits 0
   (all 20 .lean files start with `module`). The CI cmp of the definitions block between Challenge.lean
   and BLF/Defs.lean exits 0 (byte-identical).
3. Axiom collector: PASS. Verify/Axioms.lean imports BLF and Solution, enumerates every theorem whose
   name has prefix BLF in the environment (214 theorems, including auto-generated equation lemmas;
   the sources declare 193: 186 in BLF/ plus 7 in Solution.lean; 12 each in BLF.N1, N2, N3 and 104 in
   BLF.N4) and runs Lean.collectAxioms on each. Axioms seen across all: propext, Classical.choice,
   Quot.sound only; 0 violations. `#print axioms` on each of the 7 Solution theorems gives
   [propext, Classical.choice, Quot.sound]. Control: the same command on Challenge's
   BLF.blf_count_four reports sorryAx, so the collector does detect sorry.
4. Statement audit: PASS, no gap found. Details:
   - bitAt j N := N / 2^j % 2 = 1 on Int. In Lean 4 core, Int `/` and `%` are Euclidean (ediv, emod);
     for the positive divisor 2^j this is floor division and emod is in {0, 1}, so this is bit j of
     the two's complement expansion. Confirmed by kernel evaluation: bitAt 0 (-3) = true,
     bitAt 1 (-3) = false, bitAt 2 (-3) = true, bitAt 5 (-1) = true (T-division would give false
     for bitAt 0 (-3)).
   - IsBLF: existential over j : Nat, K : Int, a : Fin n -> Int with no bound on j; f equals the bit
     pointwise on all 2^n vertices. Matches the docstring.
   - Counts: Nat.card of the subtype {f : (Fin n -> Bool) -> Bool // IsBLF f}. The ambient type is
     finite (Fintype), and functions are equal by funext, so this is exactly the number of Boolean
     functions on n variables that are BLF; no degenerate Nat.card = 0 case arises.
   - floor_parallelogram: hypothesis is bval x_i + bval y_i = bval z_i + bval w_i for every i, i.e.
     x + y = z + w coordinatewise over the integers; conclusion is about lin K a v / 2^j, which is
     floor((K + a.v) / 2^j). Matches the docstring.
   - threshold_isBLF: [w0 + w.x > 0] with integer weights, strict. Every real-weight threshold
     function on the cube is of this form, and the non-strict form is covered by shifting w0, so the
     statement covers all threshold functions.
   - affB c b x := (bval c + sum bval b_i * bval x_i) % 2 = 1 with c : Bool, b : Fin n -> Bool, so it
     ranges over all 2^(n+1) GF(2)-affine functions; kernel check confirms affB false (all true) is
     the 3-variable parity. isBLF_xor_affB states closure of IsBLF under XOR with any of them.
   - Challenge.lean has `open Finset` before the definitions block and BLF/Defs.lean does not; this
     does not change elaboration, and the comparator compared the resulting constants (check 7).
5. Non-vacuity: PASS. Verify/NonVacuity.lean (in the copy) compiles with no errors. It proves:
   bit 1 of x0 + x1 + x2 + x3 is BLF (both via lin and via an explicit "weight in {2,3}" truth table
   checked with decide +kernel); constant false and constant true are BLF; there exists a 3-variable
   function that is not BLF (derived from blf_count_three, 208 < 256); the parallelogram hypothesis
   holds for pairwise distinct x = (1,0), y = (0,1), z = (0,0), w = (1,1); the bound 1 is attained for
   j = 1, K = 0, a = (1,1) on that quadruple; without the hypothesis the inequality fails
   (x = y = (1,1), z = w = (0,0), j = 0 gives 4); and concrete instantiations of floor_parallelogram
   (with negative coefficients), threshold_isBLF (majority of 3) and isBLF_xor_affB.
   Independent counts: own C program (/home/claude/vscratch/blf.c) and own Python program
   (/home/claude/vscratch/blf.py) enumerate bit j of K + a.x with K and every a_i ranging over
   Z / 2^(j+1) (exhaustive for each fixed j, since bit j depends only on N mod 2^(j+1), and the set is
   monotone in j because bit j of N is bit j+1 of 2N). Results: n=1: 4 (stable j=0..4); n=2: 16
   (from j=1 on, checked to j=5); n=3: 208 (from j=2 on, checked to j=6); n=4: 32, 384, 5248, 10368,
   10368, 10368 for j <= 0..5. Python agrees: 4, 16, 208, 10368. This confirms the lower bounds
   independently; the upper bounds rest on the Lean proof (search plus parallelogram constraints).
6. Planted errors: PASS, all four rejected, each restored afterwards (git status clean except Verify/).
   (a) 10368 -> 10367 in both Solution.lean and Challenge.lean: `lake build Solution Challenge` fails,
       "Solution.lean:55:2: Type mismatch".
   (b) one bit of one witness truth table flipped (Data4.lean line 40, entry 15): BLF.Check4 fails,
       "Check4.lean:224:2: Tactic decide proved that the proposition ... is false" (the search leaf no
       longer finds that mask). Extra variant (b2): keep the table but change that witness's K from 6
       to 7: BLF.Small4 fails at line 18 (witOk').
   (c) delete one witness entry (Data4.lean line 40): BLF.Check4 fails at line 224 (search check).
   (d) 324 -> 325 in Small4.lean cardS: BLF.Small4 fails, "(kernel) application type mismatch" at
       23:48 and unsolved goals at 31:83.
   Note: the first attempt at (d) died with exit 137 in Check4 because another build (in
   /home/claude/blf) was running concurrently in the same 6 GiB cgroup; rerun alone, Check4 built
   (peak about 3.1 GB system use) and Small4 failed as expected.
7. Comparator: PARTIAL. ./scripts/verify-comparator.sh (8 min 34 s) exit 1. Lean default kernel:
   accepts. con-ron: accepts ("accepted 14509 declarations (--verified)"). nanoda: killed by the OOM
   killer (exit 137; dmesg: "Memory cgroup out of memory: Killed process nanoda_bin, anon-rss
   6032272kB"), which the comparator prints as "nanoda kernel rejected the solution". This is a
   resource limit of this sandbox (6 GiB cgroup), not a type error. Isolation runs with the
   toolchain's leanexport and nanoda_bin: an export of the six theorems other than blf_count_four
   (60 MB) is accepted by nanoda ("Checked 15351 declarations with no typechecker errors", peak RSS
   about 120 MB); an export of blf_count_four alone (60 MB) grows to about 5.97 GB RSS over 195 s and
   is killed. So nanoda acceptance of the n = 4 count could not be established here.

## Issues and suggested fixes

1. nanoda on blf_count_four needs more than 6 GiB here (unverified whether it finishes at all).
   Suggested fixes: rerun ./scripts/verify-comparator.sh on a machine with at least 16 GB (for example
   the GitHub Actions comparator job after pushing; no runs exist yet for this repository), and record
   the nanoda peak memory and result. If memory remains high, split Check4 further (more, smaller
   pieces, or an intermediate lemma per level whose proof term is not inlined) so nanoda's peak drops,
   and confirm Palomar's resource limits accommodate it.
2. The verified snapshot is commit cb688a7. The working tree of /home/claude/blf now has uncommitted
   changes to the statement surface (IsTXA in Defs and Challenge, two new theorems, new comparator
   entries). Those need their own fresh build, hygiene, axiom, statement audit and comparator run
   before release.
3. Cosmetic: deprecation and linter warnings (push_neg to push Not, if_true to ite_true, unused simp
   args, unnecessary <;>). Harmless, but cleaning them avoids breakage on a later Mathlib bump.
4. Check4 alone uses about 3 GB while building; two concurrent builds in a 6 GiB cgroup OOM. Worth a
   note in the README for people rebuilding on small machines.

Verdict: the formalization at commit cb688a7 is sound and the statements say what they claim:
fresh build, hygiene, axioms, statement audit, non-vacuity, independent counts and all planted errors
pass; the Lean kernel and con-ron accept via the comparator. The only open item is nanoda on
blf_count_four, which ran out of memory in this 6 GiB sandbox and must be confirmed on a larger
machine.

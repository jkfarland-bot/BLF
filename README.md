# BLF: Boolean functions that are one bit of a linear form

Lean 4 / Mathlib formalization and computations accompanying Joseph S. Farland, *Boolean functions that are one bit of a linear form: a toric identity, exact counts and
asymptotics* (preprint, Zenodo, 2026, version 1.1 [doi:10.5281/zenodo.24480511](https://doi.org/10.5281/zenodo.24480511), all versions [doi:10.5281/zenodo.24467977](https://doi.org/10.5281/zenodo.24467977); software archive version 1.1.0 [doi:10.5281/zenodo.24480745](https://doi.org/10.5281/zenodo.24480745), all versions [doi:10.5281/zenodo.24466814](https://doi.org/10.5281/zenodo.24466814)). A Boolean function f of n variables is **BLF** if

    f(x) = bit j of (K + a_1 x_1 + ... + a_n x_n)

for some integers K, a_i and some bit position j. The preprint labels each of its results as
Lean-certified (proved in this repository), computer-certified (exhaustive computation with the
code in `compute/`) or proved on paper with an independent cold read; [CLAIMS.md](CLAIMS.md) gives
the map.

**AI assistance:** the Lean code, the computations and the proofs in this repository were written
by Claude (Anthropic), an AI model, which also helped draft the preprint and search the literature;
several results came from ChatGPT (OpenAI) answers that Claude checked. The formalized statements
are machine-checked in Lean 4; the rest is not. The author, Joseph S. Farland, chose the problems,
directed the work, and is responsible for its content. No external human referee has reviewed the
preprint or the formalization.

Toolchain: `leanprover/lean4:v4.35.0-rc2`, Mathlib `v4.35.0-rc2` (the versions of the Palomar
template). Every file uses Lean's module system.

```
lake exe cache get
lake build
```

No `sorry` in the development, no `native_decide`, no new axioms: every declaration depends only on
`propext`, `Classical.choice` and `Quot.sound` (`Challenge.lean` states the sixteen results with
`sorry` by design; `Solution.lean` proves them). The n = 4 checks take a few minutes of kernel time. The full
`scripts/verify-comparator.sh` run (Lean kernel, nanoda and con-ron) passes in a 6 GiB sandbox, with
peaks of about 5 GB (leanexport), 4.6 GB (con-ron) and 4.1 GB (nanoda); run one build at a time on
small machines.

**Review.** `review/lean3` is an independent audit, by a Claude agent that did not write the code, of
commit `a5d08ee` and all sixteen statements: fresh rebuild, source hygiene, axiom collector, statement
audit, non-vacuity, own recounts, seven planted errors, and the comparator with all three kernels. The
Lean sources have not changed since `a5d08ee`. Two earlier audits of earlier commits (`review/lean1`,
seven statements; `review/lean2`, nine) are kept for the record. Separately, CI verifies every push
mechanically with the toolchain's lake comparator. See `review/README.md`.

## What is proved in Lean

* **Characterization** (every n): f is BLF iff f(x) = floor(t + r.x) mod 2 for some real t and r.
* **Parallelogram inequality** (every n): for all j, K, a and cube vertices with x + y = z + w,
  the floors F(x) = (K + a.x) / 2^j satisfy |F(x) + F(y) - F(z) - F(w)| <= 1.
* **Threshold functions are BLF** (every n), and **BLF is closed under XOR with GF(2)-affine
  functions** (every n).
* **Exact counts**: |BLF(1)| = 4, |BLF(2)| = 16, |BLF(3)| = 208 and |BLF(4)| = 10368.
* **Structure for n = 3 and 4**: a function of three variables is BLF exactly when it is a
  threshold function XOR a GF(2)-affine function; for four variables the BLF functions are the
  threshold XOR affine functions together with the affine translates of bit 1 of
  x1 + x2 + x3 + x4, and that function is not itself threshold XOR affine, so exactly 32 functions
  of BLF(4) lie outside threshold XOR affine.
* **Selector lemma** (every n and j): z AND T(x) is bit j of an integer affine form in (x, z) iff
  T(x) = [tau <= w.x] with integer weights and sum |w_i| < 2^j. Example: z AND
  [x1 + 2x2 + 2x3 + 3x4 >= 5] is bit 4 and not bit 3, so no bit position j <= 3 serves every BLF
  function of five variables (j*(5) >= 4).
* **Rule 110** (through a square identity for every BLF function): two steps and three steps of
  Rule 110, as functions of their windows of 5 and 7 cells, are not BLF.

The counts rest on a general theorem (`BLF.small_count`): BLF functions are exactly those whose
canonical form (XOR with the affine function agreeing at 0 and the unit vectors) is in an explicit
list S, so their number is |S| * 2^(n+1). One direction is the parallelogram inequality plus a
verified pruned search (`BLF.search_sound`) over the normalized floor vectors, run by the kernel;
the other is an explicit witness (j, K, a) for every element of S, also checked by the kernel.

## Layout for the Palomar registry

- `Challenge.lean`: the statement surface. It imports only Mathlib, defines `bval`, `lin`, `bitAt`,
  `IsBLF`, `affB`, `IsTXA`, `eca`, `rule110Two` and `rule110Three` with docstrings, and states the
  sixteen results with `sorry`.
- `BLF/Defs.lean`: a byte-identical copy of the definitions block (checked in CI).
- `Solution.lean`: proves the sixteen statements from the development in `BLF/`.
- `comparator.json`: the theorem names; `definition_names` is empty, so Comparator checks every
  definition the statements use, body included.
- `BLF/Data1.lean` to `BLF/Data4.lean`, `BLF/Check4.lean` and `BLF/TxaData3.lean`, `BLF/TxaData4.lean`
  are generated by `scripts/gen_small.py`, `scripts/gen_split.py` and `scripts/gen_txa.py`; the
  kernel rechecks every fact in them.

## Computations (`compute/`)

C and Python programs, exact integer arithmetic, that rebuild the counts of the preprint:
|BLF(n)| = 2, 4, 16, 208, 10368, 1903808, 1359244544 (n = 0 to 6) and the toric chamber counts
R_n = 1, 1, 3, 25, 647, 59493, 21238195, by universal grids (largest minors), the
no-broken-circuit vertex formula and the parallelogram test. `results/runs_21nov.txt` records the
runs; `proofs/` and `coldread/` hold the paper proofs of the characterization and of the identity
|BLF(n)| = 2^n (R_n + 1), with the independent cold readers' reports and code.

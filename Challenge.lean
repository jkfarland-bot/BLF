module

public import Mathlib

@[expose] public section

/-!
# Boolean functions that are one bit of a linear form

This file is the statement surface for the Palomar registry. It defines, with docstrings, the
objects the results are about, using only Mathlib, and states each headline result with `sorry`.
`Solution.lean` proves every statement below with the same name and type. Its definitions come
from `BLF/Defs.lean`, a byte-identical copy of the block between the marker lines below, and
Comparator checks them against the definitions here constant by constant, bodies included.

## Objects

* `bval b` is `1` or `0`; `lin K a x` is the linear form `K + a.x` at a cube vertex `x`.
* `bitAt j N` is bit `j` of the integer `N`, that is `(N / 2^j) % 2` with floor division.
* `IsBLF f` says `f x = bit j of (K + a.x)` for some `j`, `K`, `a` (no bound on `j`).
* `affB c b` is the GF(2)-affine function `c + b.x (mod 2)`.

## Results

Each theorem's docstring names its result in the accompanying preprint (J. S. Farland, 2026).
CLAIMS.md maps every result to Lean.
-/

open Finset

-- BEGIN STATEMENT DEFINITIONS (Challenge.lean and BLF/Defs.lean must agree byte for byte)
namespace BLF

/-- The `0/1` value of a Boolean as an integer. -/
def bval (b : Bool) : ℤ := if b then 1 else 0

/-- The linear form `K + a.x` at a cube vertex `x`. -/
def lin {n : ℕ} (K : ℤ) (a : Fin n → ℤ) (x : Fin n → Bool) : ℤ :=
  K + ∑ i, a i * bval (x i)

/-- Bit `j` of an integer: `(N / 2^j) % 2`, with `Int` division rounding down (two's complement
for negative `N`). -/
def bitAt (j : ℕ) (N : ℤ) : Bool := N / 2 ^ j % 2 = 1

/-- `f` is one bit of a linear form with a free constant: `f x = bit j of (K + a.x)` for some
`j : ℕ` and integers `K`, `a_1, ..., a_n`, with no bound on `j`. -/
def IsBLF {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (j : ℕ) (K : ℤ) (a : Fin n → ℤ), ∀ x, f x = bitAt j (lin K a x)

/-- The GF(2)-affine function `c + b_1 x_1 + ... + b_n x_n (mod 2)`. -/
def affB {n : ℕ} (c : Bool) (b : Fin n → Bool) (x : Fin n → Bool) : Bool :=
  (bval c + ∑ i, bval (b i) * bval (x i)) % 2 = 1

/-- `f` is a threshold function `[w_0 + w.x > 0]` XOR a GF(2)-affine function. -/
def IsTXA {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (w0 : ℤ) (w : Fin n → ℤ) (c : Bool) (b : Fin n → Bool),
    ∀ x, f x = xor (decide (0 < w0 + ∑ i, w i * bval (x i))) (affB c b x)

/-- Elementary cellular automaton rule `R` in Wolfram's numbering: the new value of a cell with left
neighbour `l`, value `c` and right neighbour `r` is bit `4l + 2c + r` of `R`. -/
def eca (R : ℕ) (l c r : Bool) : Bool := R.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Two steps of Rule 110 as a function of a window of five cells, `x 0` leftmost. -/
def rule110Two (x : Fin 5 → Bool) : Bool :=
  eca 110 (eca 110 (x 0) (x 1) (x 2)) (eca 110 (x 1) (x 2) (x 3)) (eca 110 (x 2) (x 3) (x 4))

/-- Three steps of Rule 110 as a function of a window of seven cells, `x 0` leftmost. -/
def rule110Three (x : Fin 7 → Bool) : Bool :=
  rule110Two ![eca 110 (x 0) (x 1) (x 2), eca 110 (x 1) (x 2) (x 3), eca 110 (x 2) (x 3) (x 4),
    eca 110 (x 3) (x 4) (x 5), eca 110 (x 4) (x 5) (x 6)]

end BLF
-- END STATEMENT DEFINITIONS

namespace BLF

open Finset

/-- Parallelogram inequality (all `n`): for every bit position, constant and coefficients, the
floors `F(x) = (K + a.x) / 2^j` satisfy `|F x + F y - F z - F w| ≤ 1` whenever `x + y = z + w`
coordinatewise. -/
theorem floor_parallelogram {n : ℕ} (j : ℕ) (K : ℤ) (a : Fin n → ℤ) (x y z w : Fin n → Bool)
    (h : ∀ i, bval (x i) + bval (y i) = bval (z i) + bval (w i)) :
    |lin K a x / 2 ^ j + lin K a y / 2 ^ j - lin K a z / 2 ^ j - lin K a w / 2 ^ j| ≤ 1 := by
  sorry

/-- Every threshold function `[w_0 + w.x > 0]` is BLF (all `n`). -/
theorem threshold_isBLF {n : ℕ} (w0 : ℤ) (w : Fin n → ℤ) :
    IsBLF (fun x => decide (0 < w0 + ∑ i, w i * bval (x i))) := by
  sorry

/-- BLF is closed under XOR with GF(2)-affine functions (all `n`). -/
theorem isBLF_xor_affB {n : ℕ} {f : (Fin n → Bool) → Bool} (hf : IsBLF f) (c : Bool)
    (b : Fin n → Bool) : IsBLF (fun x => xor (f x) (affB c b x)) := by
  sorry

/-- `|BLF(1)| = 4`. -/
theorem blf_count_one : Nat.card {f : (Fin 1 → Bool) → Bool // IsBLF f} = 4 := by
  sorry

/-- `|BLF(2)| = 16`. -/
theorem blf_count_two : Nat.card {f : (Fin 2 → Bool) → Bool // IsBLF f} = 16 := by
  sorry

/-- `|BLF(3)| = 208`: 208 of the 256 Boolean functions of three variables are one bit of a
linear form. -/
theorem blf_count_three : Nat.card {f : (Fin 3 → Bool) → Bool // IsBLF f} = 208 := by
  sorry

/-- `|BLF(4)| = 10368` of the 65536 Boolean functions of four variables. -/
theorem blf_count_four : Nat.card {f : (Fin 4 → Bool) → Bool // IsBLF f} = 10368 := by
  sorry

/-- For three variables, BLF is exactly threshold XOR affine. -/
theorem blf_three_iff_threshold_xor_affine (f : (Fin 3 → Bool) → Bool) : IsBLF f ↔ IsTXA f := by
  sorry

/-- For four variables, BLF is threshold XOR affine together with the affine translates of
bit 1 of `x_1 + x_2 + x_3 + x_4`. -/
theorem blf_four_iff (f : (Fin 4 → Bool) → Bool) :
    IsBLF f ↔ IsTXA f ∨
      ∃ (c : Bool) (b : Fin 4 → Bool), ∀ x, f x = xor (bitAt 1 (∑ i, bval (x i))) (affB c b x) := by
  sorry

/-- The boundary at four variables is strict: bit 1 of `x_1 + x_2 + x_3 + x_4` is BLF but not a
threshold function XOR an affine function. -/
theorem bitOneSum_isBLF_not_txa :
    IsBLF (fun x : Fin 4 → Bool => bitAt 1 (∑ i, bval (x i))) ∧
      ¬ IsTXA (fun x : Fin 4 → Bool => bitAt 1 (∑ i, bval (x i))) := by
  sorry

/-- Characterization (Proposition 2.1, all `n`): `f` is BLF iff `f x = ⌊t + r.x⌋ mod 2` for some real
`t` and `r`. -/
theorem isBLF_iff_floor {n : ℕ} (f : (Fin n → Bool) → Bool) :
    IsBLF f ↔ ∃ (t : ℝ) (r : Fin n → ℝ),
      ∀ x, f x = decide (⌊t + ∑ i, r i * (bval (x i) : ℝ)⌋ % 2 = 1) := by
  sorry

/-- Selector lemma (Lemma 8.2, all `n` and `j`): `z ∧ T(x)` is bit `j` of an integer affine form in
`(x, z)` iff `T(x) = [τ ≤ w.x]` for integer weights with `∑ |w_i| < 2^j`. -/
theorem selector_iff {n : ℕ} (j : ℕ) (T : (Fin n → Bool) → Bool) :
    (∃ (K c : ℤ) (a : Fin n → ℤ), ∀ x z, (z && T x) = bitAt j (lin K a x + c * bval z)) ↔
      ∃ (w : Fin n → ℤ) (τ : ℤ), ∑ i, |w i| < 2 ^ j ∧
        ∀ x, T x = decide (τ ≤ ∑ i, w i * bval (x i)) := by
  sorry

/-- The gated threshold `z ∧ [x1 + 2 x2 + 2 x3 + 3 x4 ≥ 5]` (Section 8) is bit 4 of an integer
affine form and not bit 3. -/
theorem gated_threshold_bit_four :
    (∃ (K c : ℤ) (a : Fin 4 → ℤ), ∀ x z,
      (z && decide (5 ≤ bval (x 0) + 2 * bval (x 1) + 2 * bval (x 2) + 3 * bval (x 3)))
        = bitAt 4 (lin K a x + c * bval z)) ∧
    ¬ ∃ (K c : ℤ) (a : Fin 4 → ℤ), ∀ x z,
      (z && decide (5 ≤ bval (x 0) + 2 * bval (x 1) + 2 * bval (x 2) + 3 * bval (x 3)))
        = bitAt 3 (lin K a x + c * bval z) := by
  sorry

/-- No bit position `j ≤ 3` serves every BLF function of five variables: `j*(5) ≥ 4`. -/
theorem blf_five_needs_bit_four :
    ∃ f : (Fin 5 → Bool) → Bool, IsBLF f ∧
      ∀ j ≤ 3, ¬ ∃ (K : ℤ) (a : Fin 5 → ℤ), ∀ x, f x = bitAt j (lin K a x) := by
  sorry

/-- Two steps of Rule 110 are not BLF (Corollary 9.2). -/
theorem rule110Two_not_isBLF : ¬ IsBLF rule110Two := by
  sorry

/-- Three steps of Rule 110 are not BLF (Corollary 9.2). -/
theorem rule110Three_not_isBLF : ¬ IsBLF rule110Three := by
  sorry

end BLF

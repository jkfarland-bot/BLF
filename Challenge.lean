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

end BLF

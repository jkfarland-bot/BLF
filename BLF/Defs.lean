module

public import Mathlib

@[expose] public section

/-!
# Boolean functions that are one bit of a linear form: definitions

These are the definitions of the statement surface. `Challenge.lean` contains a byte-identical copy
of the block between the two marker lines (checked in CI).
-/

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

end BLF
-- END STATEMENT DEFINITIONS

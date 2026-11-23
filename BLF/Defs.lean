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

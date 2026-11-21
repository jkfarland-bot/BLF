import Mathlib

/-!
# Boolean functions that are one bit of a linear form

`IsBLF f` says that `f x = bit j of (K + a.x)` for some `j : ℕ` and integers `K`, `a_i`
(no bound on `j`); for an integer `N`, bit `j` is `(N / 2^j) % 2` with floor division
(`Int` division by a positive number rounds down), which is two's complement for negative `N`.
-/

namespace BLF

/-- `0/1` value of a Boolean as an integer. -/
def bval (b : Bool) : ℤ := if b then 1 else 0

/-- The linear form `K + a.x` at a cube vertex `x`. -/
def lin {n : ℕ} (K : ℤ) (a : Fin n → ℤ) (x : Fin n → Bool) : ℤ :=
  K + ∑ i, a i * bval (x i)

/-- Bit `j` of an integer (floor division, two's complement for negatives). -/
def bitAt (j : ℕ) (N : ℤ) : Bool := N / 2 ^ j % 2 = 1

/-- `f` is one bit of a linear form with a free constant. -/
def IsBLF {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (j : ℕ) (K : ℤ) (a : Fin n → ℤ), ∀ x, f x = bitAt j (lin K a x)

end BLF

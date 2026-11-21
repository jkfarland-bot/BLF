module

public import BLF

@[expose] public section

/-!
# Proved solution

Each headline theorem below has exactly the statement of its counterpart in `Challenge.lean`.
The definitions it uses come from `BLF/Defs.lean`, a byte-identical copy of the Challenge's
definitions, and are the definitions of the development itself, so no bridge is needed.
-/

open Finset


namespace BLF

open Finset

/-- Parallelogram inequality (all `n`): for every bit position, constant and coefficients, the
floors `F(x) = (K + a.x) / 2^j` satisfy `|F x + F y - F z - F w| ≤ 1` whenever `x + y = z + w`
coordinatewise. -/
theorem floor_parallelogram {n : ℕ} (j : ℕ) (K : ℤ) (a : Fin n → ℤ) (x y z w : Fin n → Bool)
    (h : ∀ i, bval (x i) + bval (y i) = bval (z i) + bval (w i)) :
    |lin K a x / 2 ^ j + lin K a y / 2 ^ j - lin K a z / 2 ^ j - lin K a w / 2 ^ j| ≤ 1 :=
  flo_par j K a x y z w h

/-- Every threshold function `[w_0 + w.x > 0]` is BLF (all `n`). -/
theorem threshold_isBLF {n : ℕ} (w0 : ℤ) (w : Fin n → ℤ) :
    IsBLF (fun x => decide (0 < w0 + ∑ i, w i * bval (x i))) :=
  threshold_isBLF' w0 w

/-- BLF is closed under XOR with GF(2)-affine functions (all `n`). -/
theorem isBLF_xor_affB {n : ℕ} {f : (Fin n → Bool) → Bool} (hf : IsBLF f) (c : Bool)
    (b : Fin n → Bool) : IsBLF (fun x => xor (f x) (affB c b x)) :=
  isBLF_xor_affB' hf c b

/-- `|BLF(1)| = 4`. -/
theorem blf_count_one : Nat.card {f : (Fin 1 → Bool) → Bool // IsBLF f} = 4 :=
  card_blf_one

/-- `|BLF(2)| = 16`. -/
theorem blf_count_two : Nat.card {f : (Fin 2 → Bool) → Bool // IsBLF f} = 16 :=
  card_blf_two

/-- `|BLF(3)| = 208`: 208 of the 256 Boolean functions of three variables are one bit of a
linear form. -/
theorem blf_count_three : Nat.card {f : (Fin 3 → Bool) → Bool // IsBLF f} = 208 :=
  card_blf_three

/-- `|BLF(4)| = 10368` of the 65536 Boolean functions of four variables. -/
theorem blf_count_four : Nat.card {f : (Fin 4 → Bool) → Bool // IsBLF f} = 10368 :=
  card_blf_four

end BLF

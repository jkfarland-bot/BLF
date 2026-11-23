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

/-- For three variables, BLF is exactly threshold XOR affine. -/
theorem blf_three_iff_threshold_xor_affine (f : (Fin 3 → Bool) → Bool) : IsBLF f ↔ IsTXA f :=
  blf_three_iff_txa' f

/-- For four variables, BLF is threshold XOR affine together with the affine translates of
bit 1 of `x_1 + x_2 + x_3 + x_4`. -/
theorem blf_four_iff (f : (Fin 4 → Bool) → Bool) :
    IsBLF f ↔ IsTXA f ∨
      ∃ (c : Bool) (b : Fin 4 → Bool), ∀ x, f x = xor (bitAt 1 (∑ i, bval (x i))) (affB c b x) :=
  blf_four_iff' f

/-- The boundary at four variables is strict: bit 1 of `x_1 + x_2 + x_3 + x_4` is BLF but not a
threshold function XOR an affine function. -/
theorem bitOneSum_isBLF_not_txa :
    IsBLF (fun x : Fin 4 → Bool => bitAt 1 (∑ i, bval (x i))) ∧
      ¬ IsTXA (fun x : Fin 4 → Bool => bitAt 1 (∑ i, bval (x i))) :=
  ⟨bitOneSum_isBLF, bitOneSum_not_txa'⟩

/-- Characterization (Proposition 2.1, all `n`): `f` is BLF iff `f x = ⌊t + r.x⌋ mod 2` for some real
`t` and `r`. -/
theorem isBLF_iff_floor {n : ℕ} (f : (Fin n → Bool) → Bool) :
    IsBLF f ↔ ∃ (t : ℝ) (r : Fin n → ℝ),
      ∀ x, f x = decide (⌊t + ∑ i, r i * (bval (x i) : ℝ)⌋ % 2 = 1) := by
  exact isBLF_iff_floor' f

/-- Selector lemma (Lemma 8.2, all `n` and `j`): `z ∧ T(x)` is bit `j` of an integer affine form in
`(x, z)` iff `T(x) = [τ ≤ w.x]` for integer weights with `∑ |w_i| < 2^j`. -/
theorem selector_iff {n : ℕ} (j : ℕ) (T : (Fin n → Bool) → Bool) :
    (∃ (K c : ℤ) (a : Fin n → ℤ), ∀ x z, (z && T x) = bitAt j (lin K a x + c * bval z)) ↔
      ∃ (w : Fin n → ℤ) (τ : ℤ), ∑ i, |w i| < 2 ^ j ∧
        ∀ x, T x = decide (τ ≤ ∑ i, w i * bval (x i)) := by
  exact selector_iff' j T

/-- The gated threshold `z ∧ [x1 + 2 x2 + 2 x3 + 3 x4 ≥ 5]` (Section 8) is bit 4 of an integer
affine form and not bit 3. -/
theorem gated_threshold_bit_four :
    (∃ (K c : ℤ) (a : Fin 4 → ℤ), ∀ x z,
      (z && decide (5 ≤ bval (x 0) + 2 * bval (x 1) + 2 * bval (x 2) + 3 * bval (x 3)))
        = bitAt 4 (lin K a x + c * bval z)) ∧
    ¬ ∃ (K c : ℤ) (a : Fin 4 → ℤ), ∀ x z,
      (z && decide (5 ≤ bval (x 0) + 2 * bval (x 1) + 2 * bval (x 2) + 3 * bval (x 3)))
        = bitAt 3 (lin K a x + c * bval z) := by
  exact ⟨tFC80_bit_four, tFC80_not_bit_three⟩

/-- No bit position `j ≤ 3` serves every BLF function of five variables: `j*(5) ≥ 4`. -/
theorem blf_five_needs_bit_four :
    ∃ f : (Fin 5 → Bool) → Bool, IsBLF f ∧
      ∀ j ≤ 3, ¬ ∃ (K : ℤ) (a : Fin 5 → ℤ), ∀ x, f x = bitAt j (lin K a x) := by
  exact ⟨gFC80, gFC80_isBLF, gFC80_not_low_bit⟩

/-- Two steps of Rule 110 are not BLF (Corollary 9.2). -/
theorem rule110Two_not_isBLF : ¬ IsBLF rule110Two := by
  exact rule110Two_not_isBLF'

/-- Three steps of Rule 110 are not BLF (Corollary 9.2). -/
theorem rule110Three_not_isBLF : ¬ IsBLF rule110Three := by
  exact rule110Three_not_isBLF'

end BLF

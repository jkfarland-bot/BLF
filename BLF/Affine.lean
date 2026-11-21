module

public import BLF.Basic

@[expose] public section

namespace BLF

open Finset

/-- Parity of an integer as an element of `ZMod 2`. -/
abbrev par (z : ℤ) : ZMod 2 := (z : ZMod 2)

lemma odd_iff_par (z : ℤ) : (z % 2 = 1) ↔ par z = 1 := by
  unfold par
  rcases Int.emod_two_eq_zero_or_one z with h | h
  · have hz : z = 2 * (z / 2) := by omega
    rw [h, hz]; push_cast
    simp [show (2 : ZMod 2) = 0 from rfl]
  · have hz : z = 2 * (z / 2) + 1 := by omega
    rw [h, hz]; push_cast
    simp [show (2 : ZMod 2) = 0 from rfl]

lemma bitAt_iff (j : ℕ) (N : ℤ) : bitAt j N = true ↔ par (N / 2 ^ j) = 1 := by
  unfold bitAt; rw [decide_eq_true_iff]; exact odd_iff_par _

lemma bitAt_eq_dec (j : ℕ) (N : ℤ) : bitAt j N = decide (par (N / 2 ^ j) = 1) := by
  rw [Bool.eq_iff_iff, bitAt_iff, decide_eq_true_iff]

/-- The GF(2)-affine function `c + sum b_i x_i`, as a value in `ZMod 2`. -/
def affZ {n : ℕ} (c : Bool) (b : Fin n → Bool) (x : Fin n → Bool) : ZMod 2 :=
  par (bval c) + ∑ i, par (bval (b i)) * par (bval (x i))

/-- The GF(2)-affine Boolean function with constant `c` and linear part `b`. -/
def aff {n : ℕ} (c : Bool) (b : Fin n → Bool) (x : Fin n → Bool) : Bool := decide (affZ c b x = 1)

lemma par_bval (b : Bool) : par (bval b) = if b then 1 else 0 := by cases b <;> simp [bval, par]

lemma zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by revert z; decide

/-- XOR with a GF(2)-affine function keeps BLF. -/
theorem IsBLF.xor_aff {n : ℕ} {f : (Fin n → Bool) → Bool} (hf : IsBLF f) (c : Bool)
    (b : Fin n → Bool) : IsBLF (fun x => xor (f x) (aff c b x)) := by
  obtain ⟨j, K, a, h⟩ := hf
  refine ⟨j, K + 2 ^ j * bval c, fun i => a i + 2 ^ j * bval (b i), fun x => ?_⟩
  have hd : (2 : ℤ) ^ j ≠ 0 := by positivity
  have hl : lin (K + 2 ^ j * bval c) (fun i => a i + 2 ^ j * bval (b i)) x
      = lin K a x + 2 ^ j * (bval c + ∑ i, bval (b i) * bval (x i)) := by
    unfold lin
    simp only [add_mul, sum_add_distrib, mul_add, mul_sum]
    ring_nf
  show xor (f x) (aff c b x) = _
  rw [hl, h x]
  have e : (lin K a x + 2 ^ j * (bval c + ∑ i, bval (b i) * bval (x i))) / 2 ^ j
      = lin K a x / 2 ^ j + (bval c + ∑ i, bval (b i) * bval (x i)) := by
    rw [Int.add_mul_ediv_left _ _ hd]
  have ha : affZ c b x = par (bval c + ∑ i, bval (b i) * bval (x i)) := by
    unfold affZ par; push_cast; rfl
  unfold aff
  rw [ha]
  have key : par ((lin K a x + 2 ^ j * (bval c + ∑ i, bval (b i) * bval (x i))) / 2 ^ j)
      = par (lin K a x / 2 ^ j) + par (bval c + ∑ i, bval (b i) * bval (x i)) := by
    rw [e]; unfold par; push_cast; ring
  rw [bitAt_eq_dec, bitAt_eq_dec, key]
  rcases zmod2_cases (par (lin K a x / 2 ^ j)) with h1 | h1 <;>
  rcases zmod2_cases (par (bval c + ∑ i, bval (b i) * bval (x i))) with h2 | h2 <;>
  · rw [h1, h2]; decide

end BLF

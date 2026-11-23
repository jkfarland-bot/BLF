module

public import BLF.Basic

@[expose] public section

/-!
# The characterization: BLF functions are the parities of floors of real affine functions

`f` is BLF if and only if `f x = ⌊t + r.x⌋ mod 2` for some real `t` and `r` (every `n`).
Forward: `bit j of N` is `⌊N / 2^j⌋ mod 2`. Converse: shift `t` up by half the least gap to the next
integer, so every value sits strictly inside its unit interval with margin, then round `2^j t` and
`2^j r_i` down for `j` large; the error `(n+1) / 2^j` is below the margin.
-/

namespace BLF

open Finset

/-- The real affine form `t + r.x` at a cube vertex. -/
noncomputable def ulin {n : ℕ} (t : ℝ) (r : Fin n → ℝ) (x : Fin n → Bool) : ℝ :=
  t + ∑ i, r i * (bval (x i) : ℝ)

lemma bval_real_nonneg (b : Bool) : (0 : ℝ) ≤ (bval b : ℝ) := by cases b <;> simp [bval]

lemma bval_real_le_one (b : Bool) : (bval b : ℝ) ≤ 1 := by cases b <;> simp [bval]

lemma lin_cast {n : ℕ} (K : ℤ) (a : Fin n → ℤ) (x : Fin n → Bool) :
    ((lin K a x : ℤ) : ℝ) = (K : ℝ) + ∑ i, (a i : ℝ) * (bval (x i) : ℝ) := by
  simp [lin]

/-- Integer floor division by `2^j` is the real floor of the quotient. -/
lemma floor_div_two_pow (N : ℤ) (j : ℕ) : ⌊(N : ℝ) / (2 : ℝ) ^ j⌋ = N / 2 ^ j := by
  have h := Int.floor_div_natCast (N : ℝ) (2 ^ j)
  simp only [Int.floor_intCast, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

/-- Every real affine form has the same floors on the cube as `lin K a / 2^j` for some integers. -/
lemma exists_int_floor {n : ℕ} (t : ℝ) (r : Fin n → ℝ) :
    ∃ (j : ℕ) (K : ℤ) (a : Fin n → ℤ), ∀ x, lin K a x / 2 ^ j = ⌊ulin t r x⌋ := by
  obtain ⟨x0, -, hx0⟩ := Finset.exists_min_image (univ : Finset (Fin n → Bool))
    (fun x => (⌊ulin t r x⌋ : ℝ) + 1 - ulin t r x) univ_nonempty
  set δ : ℝ := (⌊ulin t r x0⌋ : ℝ) + 1 - ulin t r x0 with hδdef
  have hδpos : 0 < δ := by have := Int.lt_floor_add_one (ulin t r x0); linarith
  have hδ : ∀ x, δ ≤ (⌊ulin t r x⌋ : ℝ) + 1 - ulin t r x := fun x => hx0 x (mem_univ x)
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (2 * ((n : ℝ) + 1) / δ) (by norm_num : (1 : ℝ) < 2)
  have hpow : (0 : ℝ) < 2 ^ j := by positivity
  have hj' : 2 * ((n : ℝ) + 1) < δ * 2 ^ j := by
    rw [div_lt_iff₀ hδpos] at hj; linarith
  refine ⟨j, ⌊2 ^ j * (t + δ / 2)⌋, fun i => ⌊2 ^ j * r i⌋, fun x => ?_⟩
  rw [← floor_div_two_pow, Int.floor_eq_iff, lin_cast]
  set N : ℝ := (⌊2 ^ j * (t + δ / 2)⌋ : ℝ) + ∑ i, ((⌊2 ^ j * r i⌋ : ℤ) : ℝ) * (bval (x i) : ℝ)
  -- bounds on each term
  have hup : N ≤ 2 ^ j * (ulin t r x + δ / 2) := by
    have h1 := Int.floor_le (2 ^ j * (t + δ / 2))
    have h2 : ∑ i, ((⌊2 ^ j * r i⌋ : ℤ) : ℝ) * (bval (x i) : ℝ)
        ≤ ∑ i, 2 ^ j * r i * (bval (x i) : ℝ) :=
      sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (Int.floor_le _) (bval_real_nonneg _)
    have h3 : ∑ i, 2 ^ j * r i * (bval (x i) : ℝ) = 2 ^ j * ∑ i, r i * (bval (x i) : ℝ) := by
      rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
    simp only [ulin, N]; nlinarith
  have hlo : 2 ^ j * (ulin t r x + δ / 2) - ((n : ℝ) + 1) < N := by
    have h1 := Int.lt_floor_add_one (2 ^ j * (t + δ / 2))
    have h2 : ∑ i, (2 ^ j * r i * (bval (x i) : ℝ) - 1)
        ≤ ∑ i, ((⌊2 ^ j * r i⌋ : ℤ) : ℝ) * (bval (x i) : ℝ) := by
      refine sum_le_sum fun i _ => ?_
      have hf := Int.lt_floor_add_one (2 ^ j * r i)
      have hb0 := bval_real_nonneg (x i)
      have hb1 := bval_real_le_one (x i)
      nlinarith
    have h3 : ∑ i, (2 ^ j * r i * (bval (x i) : ℝ) - 1)
        = 2 ^ j * ∑ i, r i * (bval (x i) : ℝ) - n := by
      rw [sum_sub_distrib, mul_sum]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      congr 1; exact sum_congr rfl fun i _ => by ring
    simp only [ulin, N]; nlinarith
  have hfl := Int.floor_le (ulin t r x)
  have hδx := hδ x
  constructor
  · rw [le_div_iff₀ hpow]; nlinarith
  · rw [div_lt_iff₀ hpow]; nlinarith

/-- **Characterization.** `f` is BLF iff `f x = ⌊t + r.x⌋ mod 2` for some real `t` and `r`. -/
theorem isBLF_iff_floor' {n : ℕ} (f : (Fin n → Bool) → Bool) :
    IsBLF f ↔ ∃ (t : ℝ) (r : Fin n → ℝ),
      ∀ x, f x = decide (⌊t + ∑ i, r i * (bval (x i) : ℝ)⌋ % 2 = 1) := by
  constructor
  · rintro ⟨j, K, a, h⟩
    refine ⟨(K : ℝ) / 2 ^ j, fun i => (a i : ℝ) / 2 ^ j, fun x => ?_⟩
    have e : (K : ℝ) / 2 ^ j + ∑ i, (a i : ℝ) / 2 ^ j * (bval (x i) : ℝ)
        = ((lin K a x : ℤ) : ℝ) / 2 ^ j := by
      rw [lin_cast, add_div, sum_div]
      congr 1; exact sum_congr rfl fun i _ => by ring
    rw [h x, e, floor_div_two_pow]
    rfl
  · rintro ⟨t, r, h⟩
    obtain ⟨j, K, a, hK⟩ := exists_int_floor t r
    refine ⟨j, K, a, fun x => ?_⟩
    rw [h x]
    have := hK x
    simp only [ulin] at this
    rw [← this]
    rfl

end BLF

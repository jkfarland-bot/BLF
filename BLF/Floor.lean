module

public import BLF.Canon

@[expose] public section

namespace BLF

open Finset

/-- Cube relation `x + y = z + w`. -/
def Rel {n : ℕ} (x y z w : Fin n → Bool) : Prop := ∀ i, bval (x i) + bval (y i) = bval (z i) + bval (w i)

/-- The normalized floor vector: `flo` minus its integer affine interpolant at `0` and the `e_i`. -/
def Gof {n : ℕ} (j : ℕ) (K : ℤ) (a : Fin n → ℤ) (x : Fin n → Bool) : ℤ :=
  flo j K a x - flo j K a v0 - ∑ i, bval (x i) * (flo j K a (ve i) - flo j K a v0)

lemma Gof_par {n : ℕ} (j : ℕ) (K : ℤ) (a : Fin n → ℤ) (x y z w : Fin n → Bool) (h : Rel x y z w) :
    |Gof j K a x + Gof j K a y - Gof j K a z - Gof j K a w| ≤ 1 := by
  have hp := flo_par j K a x y z w h
  have hs : ∑ i, bval (x i) * (flo j K a (ve i) - flo j K a v0)
      + ∑ i, bval (y i) * (flo j K a (ve i) - flo j K a v0)
      = ∑ i, bval (z i) * (flo j K a (ve i) - flo j K a v0)
      + ∑ i, bval (w i) * (flo j K a (ve i) - flo j K a v0) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← add_mul, ← add_mul, h i]
  unfold Gof
  have : flo j K a x - flo j K a v0 - ∑ i, bval (x i) * (flo j K a (ve i) - flo j K a v0)
      + (flo j K a y - flo j K a v0 - ∑ i, bval (y i) * (flo j K a (ve i) - flo j K a v0))
      - (flo j K a z - flo j K a v0 - ∑ i, bval (z i) * (flo j K a (ve i) - flo j K a v0))
      - (flo j K a w - flo j K a v0 - ∑ i, bval (w i) * (flo j K a (ve i) - flo j K a v0))
      = flo j K a x + flo j K a y - flo j K a z - flo j K a w := by linarith
  rw [this]; exact hp

lemma Gof_v0 {n : ℕ} (j : ℕ) (K : ℤ) (a : Fin n → ℤ) : Gof j K a v0 = 0 := by
  simp [Gof, v0, bval]

lemma Gof_ve {n : ℕ} (j : ℕ) (K : ℤ) (a : Fin n → ℤ) (i : Fin n) : Gof j K a (ve i) = 0 := by
  unfold Gof
  rw [Finset.sum_eq_single i]
  · simp [ve, bval]
  · intro k _ hk; simp [ve, bval, hk]
  · simp

lemma par_bval_dec (p : ZMod 2) : par (bval (decide (p = 1))) = p := by
  rcases zmod2_cases p with h | h <;> subst h <;> simp [bval, par]

/-- The parity of the normalized floor vector is the canonical form of `f`. -/
theorem canon_eq_Gof {n : ℕ} (j : ℕ) (K : ℤ) (a : Fin n → ℤ) (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, f x = bitAt j (lin K a x)) :
    canon f = fun x => decide (par (Gof j K a x) = 1) := by
  have hF : ∀ x, f x = decide (par (flo j K a x) = 1) := fun x => by rw [hf, bitAt_eq_dec]; rfl
  funext x
  have hA : affZ (f v0) (fun i => xor (f (ve i)) (f v0)) x
      = par (flo j K a v0 + ∑ i, bval (x i) * (flo j K a (ve i) - flo j K a v0)) := by
    unfold affZ
    rw [hF v0, par_bval_dec]
    have hx : ∀ b c : Bool, par (bval (xor b c)) = par (bval b) - par (bval c) := by
      intro b c; cases b <;> cases c <;> simp [bval, par] <;> decide
    have hi : ∀ i, par (bval (xor (f (ve i)) (decide (par (flo j K a v0) = 1)))) * par (bval (x i))
        = par (bval (x i) * (flo j K a (ve i) - flo j K a v0)) := by
      intro i
      rw [hx, hF (ve i), par_bval_dec, par_bval_dec]
      unfold par; push_cast; ring
    rw [Finset.sum_congr rfl (fun i _ => hi i)]
    unfold par; push_cast; rfl
  have hG : par (Gof j K a x) = par (flo j K a x)
      - par (flo j K a v0 + ∑ i, bval (x i) * (flo j K a (ve i) - flo j K a v0)) := by
    unfold Gof par; push_cast; ring
  simp only [canon, affOf, aff]
  rw [hA, hG, hF x]
  rcases zmod2_cases (par (flo j K a x)) with h1 | h1 <;>
  rcases zmod2_cases (par (flo j K a v0 + ∑ i, bval (x i) * (flo j K a (ve i) - flo j K a v0)))
    with h2 | h2 <;> rw [h1, h2] <;> decide

end BLF

module

public import BLF.Defs

@[expose] public section

namespace BLF

open Finset

/-- Floor of `lin K a x / 2^j`. -/
def flo {n : ℕ} (j : ℕ) (K : ℤ) (a : Fin n → ℤ) (x : Fin n → Bool) : ℤ := lin K a x / 2 ^ j

lemma lin_add_eq {n : ℕ} (K : ℤ) (a : Fin n → ℤ) (x y z w : Fin n → Bool)
    (h : ∀ i, bval (x i) + bval (y i) = bval (z i) + bval (w i)) :
    lin K a x + lin K a y = lin K a z + lin K a w := by
  unfold lin
  have : ∑ i, a i * bval (x i) + ∑ i, a i * bval (y i)
      = ∑ i, a i * bval (z i) + ∑ i, a i * bval (w i) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← mul_add, ← mul_add, h i]
  linarith

/-- Floors of an integer sum identity: if `A + B = C + D` then the floors by `d > 0` satisfy
`A/d + B/d ≤ C/d + D/d + 1`. -/
lemma floor_par (d A B C D : ℤ) (hd : 0 < d) (h : A + B = C + D) :
    A / d + B / d ≤ C / d + D / d + 1 := by
  have hA := Int.mul_ediv_add_emod A d
  have hB := Int.mul_ediv_add_emod B d
  have hC := Int.mul_ediv_add_emod C d
  have hD := Int.mul_ediv_add_emod D d
  have h1 := Int.emod_nonneg A hd.ne'
  have h2 := Int.emod_nonneg B hd.ne'
  have h3 := Int.emod_lt_of_pos C hd
  have h4 := Int.emod_lt_of_pos D hd
  by_contra hcon
  push_neg at hcon
  have : d * (C / d + D / d + 2) ≤ d * (A / d + B / d) :=
    mul_le_mul_of_nonneg_left (by omega) hd.le
  nlinarith

/-- **Parallelogram lemma.** For every `j, K, a` and cube vertices with `x + y = z + w`,
`|F x + F y - F z - F w| ≤ 1` where `F = flo j K a`. -/
lemma flo_par {n : ℕ} (j : ℕ) (K : ℤ) (a : Fin n → ℤ) (x y z w : Fin n → Bool)
    (h : ∀ i, bval (x i) + bval (y i) = bval (z i) + bval (w i)) :
    |flo j K a x + flo j K a y - flo j K a z - flo j K a w| ≤ 1 := by
  have hd : (0 : ℤ) < 2 ^ j := by positivity
  have e := lin_add_eq K a x y z w h
  have u := floor_par _ _ _ _ _ hd e
  have v := floor_par _ _ _ _ _ hd e.symm
  unfold flo
  rw [abs_le]; constructor <;> linarith

lemma bitAt_eq (j : ℕ) (N : ℤ) : bitAt j N = decide (N / 2 ^ j % 2 = 1) := rfl

end BLF

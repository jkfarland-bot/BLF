module

public import BLF.Txa4

@[expose] public section

/-!
# The n = 4 boundary is strict

Bit 1 of `x_1 + x_2 + x_3 + x_4` is not a threshold function XOR an affine function: on one of
eight parallelograms `x + y = z + u`, every affine translate takes the values 1, 1, 0, 0, which a
threshold function never does. (Proof written by the independent verifier seat, 21 Nov 2026.)
-/

namespace BLF

open Finset

namespace Strict

def L : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0, 7, 1, 6), (1, 6, 0, 7), (2, 5, 3, 4), (3, 4, 2, 5), (8, 15, 9, 14), (9, 14, 8, 15),
   (10, 13, 11, 12), (11, 12, 10, 13)]

theorem rel_check : ∀ q ∈ L, ∀ i : Fin 4,
    bval (vtx 4 q.1 i) + bval (vtx 4 q.2.1 i) = bval (vtx 4 q.2.2.1 i) + bval (vtx 4 q.2.2.2 i) := by
  decide +kernel

theorem fin_check : ∀ c : Bool, ∀ b : Fin 4 → Bool, (L.any fun q =>
    xor (bitOneSum (vtx 4 q.1)) (affB c b (vtx 4 q.1)) &&
    xor (bitOneSum (vtx 4 q.2.1)) (affB c b (vtx 4 q.2.1)) &&
    !(xor (bitOneSum (vtx 4 q.2.2.1)) (affB c b (vtx 4 q.2.2.1))) &&
    !(xor (bitOneSum (vtx 4 q.2.2.2)) (affB c b (vtx 4 q.2.2.2)))) = true := by
  decide +kernel

/-- A threshold function never takes the pattern 1, 1, 0, 0 on a parallelogram `x + y = z + u`. -/
theorem thr_no_square {n : ℕ} (w0 : ℤ) (w : Fin n → ℤ) (x y z u : Fin n → Bool)
    (h : ∀ i, bval (x i) + bval (y i) = bval (z i) + bval (u i))
    (hx : 0 < w0 + ∑ i, w i * bval (x i)) (hy : 0 < w0 + ∑ i, w i * bval (y i))
    (hz : ¬ 0 < w0 + ∑ i, w i * bval (z i)) (hu : ¬ 0 < w0 + ∑ i, w i * bval (u i)) : False := by
  have e : (∑ i, w i * bval (x i)) + ∑ i, w i * bval (y i) =
      (∑ i, w i * bval (z i)) + ∑ i, w i * bval (u i) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_add, ← mul_add, h i]
  omega

end Strict

/-- Bit 1 of `x_1 + x_2 + x_3 + x_4` is not threshold XOR affine. -/
theorem bitOneSum_not_txa' : ¬ IsTXA bitOneSum := by
  rintro ⟨w0, w, c, b, hf⟩
  have key : ∀ p, decide (0 < w0 + ∑ i, w i * bval (p i)) = xor (bitOneSum p) (affB c b p) := by
    intro p; rw [hf p]; simp
  obtain ⟨q, hqL, hq⟩ := List.any_eq_true.mp (Strict.fin_check c b)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hq
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hq
  rw [← key] at h1 h2 h3 h4
  exact Strict.thr_no_square w0 w _ _ _ _ (Strict.rel_check q hqL) (of_decide_eq_true h1)
    (of_decide_eq_true h2) (of_decide_eq_false h3) (of_decide_eq_false h4)

end BLF

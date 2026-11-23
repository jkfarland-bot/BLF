module

public import BLF.Selector

@[expose] public section

/-!
# A gated threshold that needs bit 4

`T(x) = [x1 + 2x2 + 2x3 + 3x4 ≥ 5]` (mask `0xfc80`) has least weight sum `8`, so `z ∧ T(x)` is bit 4
of an integer form and not bit 3 (selector lemma). Hence no bit position `j ≤ 3` serves every BLF
function of five variables.
-/

namespace BLF

open Finset

/-- The threshold `[x1 + 2 x2 + 2 x3 + 3 x4 ≥ 5]`. -/
def tFC80 (x : Fin 4 → Bool) : Bool :=
  decide (5 ≤ bval (x 0) + 2 * bval (x 1) + 2 * bval (x 2) + 3 * bval (x 3))

theorem tFC80_bit_four :
    ∃ (K c : ℤ) (a : Fin 4 → ℤ), ∀ x z, (z && tFC80 x) = bitAt 4 (lin K a x + c * bval z) :=
  ⟨7, 4, ![1, 2, 2, 3], by unfold tFC80; decide +kernel⟩

theorem tFC80_not_bit_three :
    ¬ ∃ (K c : ℤ) (a : Fin 4 → ℤ), ∀ x z, (z && tFC80 x) = bitAt 3 (lin K a x + c * bval z) := by
  intro h
  obtain ⟨w, τ, hS, hT⟩ := (selector_iff' 3 tFC80).1 h
  have e := fun x => hT x
  have h7 := e ![true, true, true, false]
  have h6 := e ![false, true, true, false]
  have h10 := e ![false, true, false, true]
  have h9 := e ![true, false, false, true]
  have h12 := e ![false, false, true, true]
  simp [tFC80, Fin.sum_univ_four, bval] at h7 h6 h10 h9 h12
  simp only [Fin.sum_univ_four] at hS
  have a0 := le_abs_self (w 0); have a1 := le_abs_self (w 1)
  have a2 := le_abs_self (w 2); have a3 := le_abs_self (w 3)
  norm_num at hS
  omega

/-- The five-variable function `x5 ∧ [x1 + 2x2 + 2x3 + 3x4 ≥ 5]`. -/
def gFC80 (y : Fin 5 → Bool) : Bool := y 4 && tFC80 (fun i => y i.castSucc)

lemma lin_snoc (K : ℤ) (a : Fin 5 → ℤ) (x : Fin 4 → Bool) (z : Bool) :
    lin K a (Fin.snoc x z : Fin 5 → Bool) = lin K (fun i => a i.castSucc) x + a (Fin.last 4) * bval z := by
  unfold lin; rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc (α := fun _ => Bool), Fin.snoc_last (α := fun _ => Bool)]; ring

theorem gFC80_isBLF : IsBLF gFC80 :=
  ⟨4, 7, ![1, 2, 2, 3, 4], by unfold gFC80 tFC80; decide +kernel⟩

/-- No bit position `j ≤ 3` realizes `gFC80`, so none serves all of `BLF(5)`. -/
theorem gFC80_not_low_bit (j : ℕ) (hj : j ≤ 3) :
    ¬ ∃ (K : ℤ) (a : Fin 5 → ℤ), ∀ y, gFC80 y = bitAt j (lin K a y) := by
  rintro ⟨K, a, h⟩
  apply tFC80_not_bit_three
  obtain ⟨m, hm⟩ : ∃ m, 3 = j + m := ⟨3 - j, by omega⟩
  rw [hm]
  refine ⟨2 ^ m * K, 2 ^ m * a (Fin.last 4), fun i => 2 ^ m * a i.castSucc, fun x z => ?_⟩
  have hy := h (Fin.snoc x z)
  have hg : gFC80 (Fin.snoc x z) = (z && tFC80 x) := by
    simp only [gFC80]
    have : (Fin.snoc x z : Fin 5 → Bool) 4 = z := by
      exact Fin.snoc_last (α := fun _ => Bool) (p := x) (x := z)
    rw [this]; congr 2; funext i; simp
  rw [← hg, hy, lin_snoc, ← bitAt_shift j m]
  congr 1; unfold lin; rw [mul_add, mul_add, mul_sum]; ring_nf

end BLF

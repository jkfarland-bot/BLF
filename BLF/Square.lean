module

public import BLF.Basic

@[expose] public section

/-!
# The square identity and Rule 110

If `f` is bit `j` of `K + a.x`, write `a_l = 2^j b_l + s_l` with `0 ≤ s_l < 2^j` (and the same for `K`).
Then `(K + a.x) / 2^j = B(x) + G(x)` with `B` integer affine and `G(x) = (s_0 + s.x) / 2^j`, and `G`
rises by `0` or `1` along every edge. The rise is the XOR of the values of `f` at the ends and of the
parity of `b_l`, and the two monotone paths across a square rise by the same total. Two and three steps
of Rule 110 violate this on the square of their last two inputs.
-/

namespace BLF

open Finset

/-- The square identity with edge parities `βi`, `βk`: values `f00, f01, f10, f11` at `p`, `p + e_k`,
`p + e_i`, `p + e_i + e_k`. -/
def sqOk (βi βk f00 f01 f10 f11 : Bool) : Prop :=
  (xor (xor f00 f01) βk).toNat + (xor (xor f01 f11) βi).toNat =
    (xor (xor f00 f10) βi).toNat + (xor (xor f10 f11) βk).toNat

instance (βi βk f00 f01 f10 f11 : Bool) : Decidable (sqOk βi βk f00 f01 f10 f11) := by
  unfold sqOk; infer_instance

lemma sum_update_true {n : ℕ} (c : Fin n → ℤ) (p : Fin n → Bool) (l : Fin n) (hl : p l = false) :
    ∑ i, c i * bval (Function.update p l true i) = ∑ i, c i * bval (p i) + c l := by
  have : ∑ i, c i * bval (Function.update p l true i) - ∑ i, c i * bval (p i) = c l := by
    rw [← sum_sub_distrib, sum_eq_single l]
    · simp [hl, bval]
    · intro i _ hi; simp [Function.update_of_ne hi]
    · simp
  linarith

/-- The parity bookkeeping of one edge. -/
lemma edge_toNat (A b D : ℤ) (hD : D = 0 ∨ D = 1) :
    ((xor (xor (decide (A % 2 = 1)) (decide ((A + b + D) % 2 = 1))) (decide (b % 2 = 1))).toNat : ℤ)
      = D := by
  rcases Int.emod_two_eq_zero_or_one A with hA | hA <;>
  rcases Int.emod_two_eq_zero_or_one b with hb | hb <;>
  rcases hD with rfl | rfl <;>
  · have h3 : (A + b + 0) % 2 = (A % 2 + b % 2) % 2 ∧ (A + b + 1) % 2 = (A % 2 + b % 2 + 1) % 2 :=
      ⟨by omega, by omega⟩
    simp [hA, hb, h3.1, h3.2] <;> omega

/-- **Square identity.** For a BLF function and two distinct coordinates `i`, `k` there are parities
`βi`, `βk` such that every square in the directions `i`, `k` satisfies `sqOk`. -/
theorem square_parity {n : ℕ} {f : (Fin n → Bool) → Bool} (hf : IsBLF f) (i k : Fin n)
    (hik : i ≠ k) : ∃ βi βk : Bool, ∀ p : Fin n → Bool, p i = false → p k = false →
      sqOk βi βk (f p) (f (Function.update p k true)) (f (Function.update p i true))
        (f (Function.update (Function.update p i true) k true)) := by
  obtain ⟨j, K, a, h⟩ := hf
  have hq : (0 : ℤ) < 2 ^ j := by positivity
  set q : ℤ := 2 ^ j with hqdef
  let B : (Fin n → Bool) → ℤ := fun x => K / q + ∑ l, a l / q * bval (x l)
  let Φ : (Fin n → Bool) → ℤ := fun x => K % q + ∑ l, a l % q * bval (x l)
  let G : (Fin n → Bool) → ℤ := fun x => Φ x / q
  have hsplit : ∀ x, lin K a x / q = B x + G x := by
    intro x
    have e : ∀ l, a l * bval (x l) = a l % q * bval (x l) + q * (a l / q * bval (x l)) := fun l => by
      have := Int.mul_ediv_add_emod (a l) q; linear_combination (-(bval (x l))) * this
    have hK := Int.mul_ediv_add_emod K q
    have : lin K a x = Φ x + q * B x := by
      simp only [lin, Φ, B]
      rw [sum_congr rfl (fun l _ => e l), sum_add_distrib, ← mul_sum]
      linear_combination (-1 : ℤ) * hK
    rw [this, Int.add_mul_ediv_left _ _ hq.ne']; simp only [G]; ring
  have hf' : ∀ x, f x = decide ((B x + G x) % 2 = 1) := by
    intro x; rw [h x, ← hsplit x]; rfl
  have hB : ∀ p l, p l = false → B (Function.update p l true) = B p + a l / q := by
    intro p l hl; simp only [B]; rw [sum_update_true _ _ _ hl]; ring
  have hΦ : ∀ p l, p l = false → Φ (Function.update p l true) = Φ p + a l % q := by
    intro p l hl; simp only [Φ]; rw [sum_update_true _ _ _ hl]; ring
  have hG : ∀ p l, p l = false →
      G (Function.update p l true) - G p = 0 ∨ G (Function.update p l true) - G p = 1 := by
    intro p l hl
    simp only [G]; rw [hΦ p l hl]
    have s1 := Int.emod_nonneg (a l) hq.ne'
    have s2 := Int.emod_lt_of_pos (a l) hq
    have e1 := Int.mul_ediv_add_emod (Φ p) q
    have e2 := Int.mul_ediv_add_emod (Φ p + a l % q) q
    have r1 := Int.emod_nonneg (Φ p) hq.ne'
    have r2 := Int.emod_lt_of_pos (Φ p) hq
    have r3 := Int.emod_nonneg (Φ p + a l % q) hq.ne'
    have r4 := Int.emod_lt_of_pos (Φ p + a l % q) hq
    have hlt : (Φ p + a l % q) / q - Φ p / q < 2 := by
      by_contra hc; push Not at hc
      have : q * 2 ≤ q * ((Φ p + a l % q) / q - Φ p / q) := mul_le_mul_of_nonneg_left hc hq.le
      nlinarith
    have hge : 0 ≤ (Φ p + a l % q) / q - Φ p / q := by
      by_contra hc; push Not at hc
      have : q * ((Φ p + a l % q) / q - Φ p / q) ≤ q * (-1) :=
        mul_le_mul_of_nonneg_left (by omega) hq.le
      nlinarith
    omega
  -- the edge rise as a Boolean expression
  have hedge : ∀ p l, p l = false →
      ((xor (xor (f p) (f (Function.update p l true))) (decide (a l / q % 2 = 1))).toNat : ℤ)
        = G (Function.update p l true) - G p := by
    intro p l hl
    rw [hf' p, hf' (Function.update p l true), hB p l hl]
    have := edge_toNat (B p + G p) (a l / q) (G (Function.update p l true) - G p) (hG p l hl)
    rw [show B p + G p + a l / q + (G (Function.update p l true) - G p)
      = B p + a l / q + G (Function.update p l true) by ring] at this
    exact this
  refine ⟨decide (a i / q % 2 = 1), decide (a k / q % 2 = 1), fun p hpi hpk => ?_⟩
  have hki : Function.update p k true i = false := by rw [Function.update_of_ne hik]; exact hpi
  have hik' : Function.update p i true k = false := by rw [Function.update_of_ne hik.symm]; exact hpk
  have comm : Function.update (Function.update p k true) i true
      = Function.update (Function.update p i true) k true := Function.update_comm hik.symm _ _ _
  have d1 := hedge p k hpk
  have d2 := hedge (Function.update p k true) i hki
  have d3 := hedge p i hpi
  have d4 := hedge (Function.update p i true) k hik'
  rw [comm] at d2
  unfold sqOk
  have hsum : ((xor (xor (f p) (f (Function.update p k true))) (decide (a k / q % 2 = 1))).toNat : ℤ)
      + (xor (xor (f (Function.update p k true)) (f (Function.update (Function.update p i true) k true)))
          (decide (a i / q % 2 = 1))).toNat
      = (xor (xor (f p) (f (Function.update p i true))) (decide (a i / q % 2 = 1))).toNat
      + (xor (xor (f (Function.update p i true)) (f (Function.update (Function.update p i true) k true)))
          (decide (a k / q % 2 = 1))).toNat := by
    rw [d1, d2, d3, d4]; ring
  exact_mod_cast hsum

end BLF

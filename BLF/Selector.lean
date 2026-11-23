module

public import BLF.Basic

@[expose] public section

/-!
# The selector lemma

`z ∧ T(x)` is bit `j` of an integer affine form in `(x, z)` if and only if `T(x) = [τ ≤ w.x]` for
integer weights with `∑ |w_i| < 2^j` (every `n`, every `j`, every `T`).
-/

namespace BLF

open Finset

lemma ediv_eq_of_bounds {q k v : ℤ} (hq : 0 < q) (h1 : q * k ≤ v) (h2 : v < q * (k + 1)) :
    v / q = k :=
  ((Int.ediv_emod_unique (r := v - q * k) hq).2 ⟨by ring, by linarith, by linarith⟩).1

lemma bitAt_def (j : ℕ) (N : ℤ) : bitAt j N = decide (N / 2 ^ j % 2 = 1) := rfl

/-- Bit `j` depends only on `N` modulo `2^(j+1)`. -/
lemma bitAt_add_mul (j : ℕ) (N m : ℤ) : bitAt j (N + 2 * 2 ^ j * m) = bitAt j N := by
  have hq : (2 : ℤ) ^ j ≠ 0 := by positivity
  rw [bitAt_def, bitAt_def]
  have : (N + 2 * 2 ^ j * m) / 2 ^ j = N / 2 ^ j + 2 * m := by
    rw [show N + 2 * 2 ^ j * m = N + 2 ^ j * (2 * m) by ring, Int.add_mul_ediv_left _ _ hq]
  rw [this]; congr 1; apply propext; omega

/-- Bit `j` of `N` is bit `j + m` of `2^m N`. -/
lemma bitAt_shift (j m : ℕ) (N : ℤ) : bitAt (j + m) (2 ^ m * N) = bitAt j N := by
  rw [bitAt_def, bitAt_def, pow_add, mul_comm ((2 : ℤ) ^ j), Int.mul_ediv_mul_of_pos _ _ (by positivity)]

lemma bval_cases (b : Bool) : bval b = 0 ∨ bval b = 1 := by cases b <;> simp [bval]

/-- The vertex agreeing with `x` on coordinates below `k` and `false` elsewhere. -/
def pre {n : ℕ} (k : ℕ) (x : Fin n → Bool) : Fin n → Bool := fun i => x i && decide (i.val < k)

lemma lin_pre_zero {n : ℕ} (K : ℤ) (a : Fin n → ℤ) (x : Fin n → Bool) : lin K a (pre 0 x) = K := by
  simp [lin, pre, bval]

lemma lin_pre_all {n : ℕ} (K : ℤ) (a : Fin n → ℤ) (x : Fin n → Bool) : lin K a (pre n x) = lin K a x := by
  have : pre n x = x := funext fun i => by simp [pre, i.isLt]
  rw [this]

lemma lin_pre_succ {n : ℕ} (K : ℤ) (a : Fin n → ℤ) (x : Fin n → Bool) (k : ℕ) (hk : k < n) :
    lin K a (pre (k + 1) x) = lin K a (pre k x) + a ⟨k, hk⟩ * bval (x ⟨k, hk⟩) := by
  unfold lin
  have : ∑ i, a i * bval (pre (k + 1) x i) - ∑ i, a i * bval (pre k x i)
      = a ⟨k, hk⟩ * bval (x ⟨k, hk⟩) := by
    rw [← sum_sub_distrib, sum_eq_single ⟨k, hk⟩]
    · simp [pre, bval]
    · intro i _ hi
      have : i.val ≠ k := fun h => hi (Fin.ext h)
      by_cases h1 : i.val < k
      · simp [pre, h1, show i.val < k + 1 by omega]
      · simp [pre, h1, show ¬ i.val < k + 1 by omega]
    · simp
  linarith

/-- Two even floors of `A` and `A + d` by `q`, with `|d| ≤ q`, are equal. -/
lemma ediv_even_step {q A d : ℤ} (hq : 0 < q) (hd1 : -q ≤ d) (hd2 : d ≤ q)
    (h1 : A / q % 2 = 0) (h2 : (A + d) / q % 2 = 0) : (A + d) / q = A / q := by
  have e1 := Int.mul_ediv_add_emod A q
  have e2 := Int.mul_ediv_add_emod (A + d) q
  have r1 := Int.emod_nonneg A hq.ne'
  have r2 := Int.emod_lt_of_pos A hq
  have r3 := Int.emod_nonneg (A + d) hq.ne'
  have r4 := Int.emod_lt_of_pos (A + d) hq
  have hlt : (A + d) / q - A / q < 2 := by
    by_contra hc; push Not at hc
    have : q * 2 ≤ q * ((A + d) / q - A / q) := mul_le_mul_of_nonneg_left hc hq.le
    nlinarith
  have hgt : -2 < (A + d) / q - A / q := by
    by_contra hc; push Not at hc
    have : q * ((A + d) / q - A / q) ≤ q * (-2) := mul_le_mul_of_nonneg_left hc hq.le
    nlinarith
  omega

/-- **Selector lemma** (necessity and sufficiency, every `n`). -/
theorem selector_iff' {n : ℕ} (j : ℕ) (T : (Fin n → Bool) → Bool) :
    (∃ (K c : ℤ) (a : Fin n → ℤ), ∀ x z, (z && T x) = bitAt j (lin K a x + c * bval z)) ↔
      ∃ (w : Fin n → ℤ) (τ : ℤ), ∑ i, |w i| < 2 ^ j ∧
        ∀ x, T x = decide (τ ≤ ∑ i, w i * bval (x i)) := by
  have hq : (0 : ℤ) < 2 ^ j := by positivity
  set q : ℤ := 2 ^ j with hqdef
  constructor
  · rintro ⟨K, c, a, h⟩
    -- reduce the coefficients into [-q, q)
    set a' : Fin n → ℤ := fun i => (a i + q) % (2 * q) - q with ha'
    have ha'lo : ∀ i, -q ≤ a' i := fun i => by
      have := Int.emod_nonneg (a i + q) (by positivity : (2 * q) ≠ 0); simp only [ha']; linarith
    have ha'hi : ∀ i, a' i < q := fun i => by
      have := Int.emod_lt_of_pos (a i + q) (by positivity : 0 < 2 * q); simp only [ha']; linarith
    have hdiff : ∀ i, a i = a' i + 2 * q * ((a i + q) / (2 * q)) := fun i => by
      have := Int.mul_ediv_add_emod (a i + q) (2 * q); simp only [ha']; linarith
    have hlin : ∀ x, lin K a x = lin K a' x + 2 * q * ∑ i, (a i + q) / (2 * q) * bval (x i) := by
      intro x; unfold lin; rw [mul_sum, add_assoc, ← sum_add_distrib]
      congr 1; exact sum_congr rfl fun i _ => by linear_combination (bval (x i)) * hdiff i
    have h' : ∀ x z, (z && T x) = bitAt j (lin K a' x + c * bval z) := by
      intro x z
      rw [h x z, hlin x, show lin K a' x + 2 * q * ∑ i, (a i + q) / (2 * q) * bval (x i) + c * bval z
        = lin K a' x + c * bval z + 2 * 2 ^ j * ∑ i, (a i + q) / (2 * q) * bval (x i) by ring,
        bitAt_add_mul]
    -- face z = 0: all floors are equal
    have heven : ∀ x, lin K a' x / q % 2 = 0 := by
      intro x
      have h0 := h' x false
      rw [show bval false = 0 from rfl, mul_zero, add_zero, bitAt_def, Bool.false_and] at h0
      have h2 := of_decide_eq_false h0.symm
      rw [← hqdef] at h2
      rcases Int.emod_two_eq_zero_or_one (lin K a' x / q) with h3 | h3
      · exact h3
      · exact absurd h3 h2
    have hconst : ∀ x, lin K a' x / q = K / q := by
      intro x
      have step : ∀ k, k ≤ n → lin K a' (pre k x) / q = K / q := by
        intro k
        induction k with
        | zero => intro _; rw [lin_pre_zero]
        | succ k ih =>
          intro hk
          have hk' : k < n := by omega
          rw [lin_pre_succ K a' x k hk', ← ih (by omega)]
          have hd := bval_cases (x ⟨k, hk'⟩)
          apply ediv_even_step hq
          · rcases hd with hd | hd <;> rw [hd] <;> [simp; linarith [ha'lo ⟨k, hk'⟩]] <;> linarith
          · rcases hd with hd | hd <;> rw [hd] <;> [simp; linarith [ha'hi ⟨k, hk'⟩]] <;> linarith
          · exact heven _
          · rw [← lin_pre_succ K a' x k hk']; exact heven _
      have := step n le_rfl
      rwa [lin_pre_all] at this
    -- the span of the z = 0 face is below q
    set xp : Fin n → Bool := fun i => decide (0 < a' i)
    set xm : Fin n → Bool := fun i => decide (a' i < 0)
    have hspan : lin K a' xp - lin K a' xm = ∑ i, |a' i| := by
      unfold lin; rw [add_sub_add_left_eq_sub, ← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      rcases lt_trichotomy (a' i) 0 with hlt | heq | hgt
      · simp [xp, xm, hlt, not_lt.2 hlt.le, bval, abs_of_neg hlt]
      · simp [xp, xm, heq, bval]
      · simp [xp, xm, hgt, not_lt.2 hgt.le, bval, abs_of_pos hgt]
    have hbox : ∀ x, q * (K / q) ≤ lin K a' x ∧ lin K a' x < q * (K / q) + q := by
      intro x
      have e := Int.mul_ediv_add_emod (lin K a' x) q
      have r1 := Int.emod_nonneg (lin K a' x) hq.ne'
      have r2 := Int.emod_lt_of_pos (lin K a' x) hq
      rw [hconst x] at e; constructor <;> linarith
    have hS : ∑ i, |a' i| < q := by
      have := hbox xp; have := hbox xm; linarith
    -- face z = 1: values lie in [B, B + S]
    have hlow : ∀ x, lin K a' xm ≤ lin K a' x := by
      intro x; unfold lin; refine add_le_add le_rfl (sum_le_sum fun i _ => ?_)
      rcases bval_cases (x i) with hb | hb <;> rw [hb] <;>
        by_cases hneg : a' i < 0 <;> simp [xm, hneg, bval] <;> linarith
    have hhigh' : ∀ x, lin K a' x ≤ lin K a' xp := by
      intro x; unfold lin; refine add_le_add le_rfl (sum_le_sum fun i _ => ?_)
      rcases bval_cases (x i) with hb | hb <;> rw [hb] <;>
        by_cases hpos : 0 < a' i <;> simp [xp, hpos, bval] <;> linarith
    have hhigh : ∀ x, lin K a' x ≤ lin K a' xm + ∑ i, |a' i| := fun x => by
      linarith [hhigh' x]
    set B := lin K a' xm + c
    set Qb := B / q
    have hB := Int.mul_ediv_add_emod B q
    have hB1 := Int.emod_nonneg B hq.ne'
    have hB2 := Int.emod_lt_of_pos B hq
    have hquot : ∀ x, (lin K a' x + c) / q =
        if q * (Qb + 1) ≤ lin K a' x + c then Qb + 1 else Qb := by
      intro x
      have l1 := hlow x; have l2 := hhigh x
      split_ifs with hM
      · apply ediv_eq_of_bounds hq hM; nlinarith
      · push Not at hM; apply ediv_eq_of_bounds hq _ (by linarith); linarith
    have hT : ∀ x, T x = bitAt j (lin K a' x + c) := by
      intro x; have h0 := h' x true
      rwa [show bval true = 1 from rfl, mul_one, Bool.true_and] at h0
    rcases Int.emod_two_eq_zero_or_one Qb with he | ho
    · refine ⟨a', q * (Qb + 1) - K - c, hS, fun x => ?_⟩
      rw [hT x, bitAt_def, ← hqdef, hquot x]
      unfold lin
      generalize q * (Qb + 1) = M
      split_ifs with hM
      · simp only [decide_eq_decide]; constructor <;> intro <;> omega
      · simp only [decide_eq_decide]; constructor <;> intro <;> omega
    · refine ⟨fun i => -a' i, K + c - q * (Qb + 1) + 1, by simpa using hS, fun x => ?_⟩
      rw [hT x, bitAt_def, ← hqdef, hquot x]
      have : ∑ i, -a' i * bval (x i) = -∑ i, a' i * bval (x i) := by
        rw [← sum_neg_distrib]; exact sum_congr rfl fun i _ => by ring
      rw [this]
      unfold lin
      generalize q * (Qb + 1) = M
      split_ifs with hM
      · simp only [decide_eq_decide]; constructor <;> intro <;> omega
      · simp only [decide_eq_decide]; constructor <;> intro <;> omega
  · rintro ⟨w, τ, hS, hT⟩
    set L : ℤ := ∑ i, min 0 (w i)
    set U : ℤ := ∑ i, max 0 (w i)
    have hUL : U - L = ∑ i, |w i| := by
      rw [← sum_sub_distrib]; refine sum_congr rfl fun i _ => ?_
      rcases le_total 0 (w i) with h | h
      · simp [h, abs_of_nonneg h]
      · simp [h, abs_of_nonpos h]
    have hsL : ∀ x : Fin n → Bool, L ≤ ∑ i, w i * bval (x i) := fun x => sum_le_sum fun i _ => by
      rcases bval_cases (x i) with hb | hb <;> rw [hb] <;> simp [min_le_left, min_le_right]
    have hsU : ∀ x : Fin n → Bool, ∑ i, w i * bval (x i) ≤ U := fun x => sum_le_sum fun i _ => by
      rcases bval_cases (x i) with hb | hb <;> rw [hb] <;> simp [le_max_left, le_max_right]
    set τ' : ℤ := max L (min τ (U + 1))
    refine ⟨-L, q + L - τ', w, fun x z => ?_⟩
    have l1 := hsL x; have l2 := hsU x
    unfold lin
    cases z
    · rw [show bval false = 0 from rfl, mul_zero, add_zero, bitAt_def, ← hqdef, Bool.false_and]
      rw [ediv_eq_of_bounds hq (k := 0) (by linarith) (by linarith)]; rfl
    · rw [show bval true = 1 from rfl, mul_one, bitAt_def, ← hqdef, Bool.true_and, hT x]
      by_cases hle : τ ≤ ∑ i, w i * bval (x i)
      · rw [ediv_eq_of_bounds hq (k := 1)]
        · simp [hle]
        · have : τ' ≤ ∑ i, w i * bval (x i) := by omega
          linarith
        · have : L ≤ τ' := le_max_left _ _
          linarith
      · rw [ediv_eq_of_bounds hq (k := 0)]
        · simp [hle]
        · have : τ' ≤ U + 1 := max_le (by linarith) (min_le_right _ _)
          linarith
        · have : ∑ i, w i * bval (x i) < τ' := by omega
          linarith

end BLF

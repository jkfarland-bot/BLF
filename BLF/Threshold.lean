module

public import BLF.Affine

@[expose] public section

namespace BLF

open Finset

lemma ediv_eq_neg_one {M d : ℤ} (hd : 0 < d) (h1 : -d ≤ M) (h2 : M < 0) : M / d = -1 :=
  ((Int.ediv_emod_unique (r := M + d) hd).mpr ⟨by ring, by linarith, by linarith⟩).1

/-- **Every threshold function is BLF** (any `n`): `[w_0 + w.x > 0]` is bit `j` of
`1 - 2 (w_0 + w.x)` for `2^j > 2 (|w_0| + sum |w_i|) + 1`. -/
theorem threshold_isBLF' {n : ℕ} (w0 : ℤ) (w : Fin n → ℤ) :
    IsBLF (fun x => decide (0 < w0 + ∑ i, w i * bval (x i))) := by
  set C : ℤ := |w0| + ∑ i, |w i| with hC
  have hC0 : 0 ≤ C := by positivity
  set j : ℕ := 2 * C.toNat + 2 with hj
  have hpow : (2 * C + 1 : ℤ) < 2 ^ j := by
    have h := (Nat.lt_two_pow_self (n := j))
    have h' : ((j : ℕ) : ℤ) < ((2 ^ j : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at h'
    have : (j : ℤ) = 2 * C + 2 := by rw [hj]; push_cast; rw [Int.toNat_of_nonneg hC0]
    linarith
  refine ⟨j, 1 - 2 * w0, fun i => -2 * w i, fun x => ?_⟩
  show decide (0 < w0 + ∑ i, w i * bval (x i)) = _
  set N : ℤ := w0 + ∑ i, w i * bval (x i) with hN
  have hbound : |N| ≤ C := by
    have hs : |∑ i, w i * bval (x i)| ≤ ∑ i, |w i| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      have : |bval (x i)| ≤ 1 := by cases x i <;> simp [bval]
      calc |w i| * |bval (x i)| ≤ |w i| * 1 := by gcongr
        _ = |w i| := by ring
    calc |N| ≤ |w0| + |∑ i, w i * bval (x i)| := abs_add_le _ _
      _ ≤ C := by rw [hC]; linarith
  have hl : lin (1 - 2 * w0) (fun i => -2 * w i) x = 1 - 2 * N := by
    unfold lin; rw [hN, mul_add, Finset.mul_sum]
    simp only [neg_mul, Finset.sum_neg_distrib, mul_assoc]; ring
  rw [hl, abs_le] at *
  have hd : (0 : ℤ) < 2 ^ j := by positivity
  unfold bitAt
  by_cases hpos : 0 < N
  · rw [ediv_eq_neg_one hd (by linarith) (by linarith)]
    simp [hpos]
  · rw [Int.ediv_eq_zero_of_lt (by linarith) (by linarith)]
    simp [hpos]

end BLF

namespace BLF

open Finset

lemma aff_eq_affB {n : ℕ} (c : Bool) (b : Fin n → Bool) (x : Fin n → Bool) :
    aff c b x = affB c b x := by
  unfold aff affB affZ
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, odd_iff_par]
  unfold par; push_cast; rfl

/-- XOR with a GF(2)-affine function keeps BLF (statement form). -/
theorem isBLF_xor_affB' {n : ℕ} {f : (Fin n → Bool) → Bool} (hf : IsBLF f) (c : Bool)
    (b : Fin n → Bool) : IsBLF (fun x => xor (f x) (affB c b x)) := by
  have := hf.xor_aff c b
  simpa [aff_eq_affB] using this

end BLF

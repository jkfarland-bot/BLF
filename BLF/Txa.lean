module

public import BLF.Small
public import BLF.Threshold

@[expose] public section

/-!
# Threshold XOR affine: classification of BLF(n) for small n from witnesses

`classify`: if every canonical BLF class is witnessed either as a threshold function XOR an affine
function or as `g` XOR an affine function (for a fixed BLF function `g`), then a function is BLF
exactly when it has one of these two forms.
-/

namespace BLF

open Finset

lemma affB_xor {n : ℕ} (c c' : Bool) (b b' : Fin n → Bool) (x : Fin n → Bool) :
    xor (affB c b x) (affB c' b' x) = affB (xor c c') (fun i => xor (b i) (b' i)) x := by
  rw [← aff_eq_affB, ← aff_eq_affB, ← aff_eq_affB]
  unfold aff affZ
  have hx : ∀ u v : Bool, par (bval (xor u v)) = par (bval u) + par (bval v) := by
    intro u v; cases u <;> cases v <;> simp [bval, par] <;> decide
  simp only [hx, add_mul, Finset.sum_add_distrib]
  set A := par (bval c) + ∑ i, par (bval (b i)) * par (bval (x i))
  set B := par (bval c') + ∑ i, par (bval (b' i)) * par (bval (x i))
  have : par (bval c) + par (bval c') + (∑ i, par (bval (b i)) * par (bval (x i)) +
      ∑ i, par (bval (b' i)) * par (bval (x i))) = A + B := by simp only [A, B]; ring
  rw [this]
  rcases zmod2_cases A with h | h <;> rcases zmod2_cases B with h' | h' <;> rw [h, h'] <;> decide

lemma affOf_eq_affB {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    affOf f x = affB (f v0) (fun i => xor (f (ve i)) (f v0)) x := aff_eq_affB _ _ _

/-- Threshold witness: truth table, `w0`, weights, affine constant, affine linear part. -/
abbrev TW := List Bool × ℤ × List ℤ × Bool × List Bool

/-- Special witness: truth table, affine constant, affine linear part. -/
abbrev SP := List Bool × Bool × List Bool

def affL (n : ℕ) (c : Bool) (b : List Bool) (k : ℕ) : Bool :=
  decide ((bval c + ((List.finRange n).map fun i : Fin n => bval (b.getD i.val false) *
    bval (vtx n k i)).sum) % 2 = 1)

def twOk (n : ℕ) (t : TW) : Bool :=
  (List.range (2 ^ n)).all fun k => t.1.getD k false ==
    xor (decide (0 < t.2.1 + ((List.finRange n).map fun i : Fin n => t.2.2.1.getD i.val 0 *
      bval (vtx n k i)).sum)) (affL n t.2.2.2.1 t.2.2.2.2 k)

def spOk (n : ℕ) (g : (Fin n → Bool) → Bool) (t : SP) : Bool :=
  (List.range (2 ^ n)).all fun k => t.1.getD k false == xor (g (vtx n k)) (affL n t.2.1 t.2.2 k)

lemma affL_eq {n : ℕ} (c : Bool) (b : List Bool) (x : Fin n → Bool) (hv : vtx n (idx x) = x) :
    affL n c b (idx x) = affB c (fun i => b.getD i.val false) x := by
  unfold affL affB; rw [hv]; congr 2

/-- Linear coverage check: walks the class list in order, matching each class with the next
threshold witness or the next special witness. -/
def coverB : List (List Bool) → List TW → List SP → Bool
  | [], _, _ => true
  | l :: ls, ts, ss =>
    match ts, ss with
    | t :: ts', s :: ss' =>
      if t.1 == l then coverB ls ts' (s :: ss') else (s.1 == l && coverB ls (t :: ts') ss')
    | t :: ts', [] => t.1 == l && coverB ls ts' []
    | [], s :: ss' => s.1 == l && coverB ls [] ss'
    | [], [] => false

lemma coverB_sound : ∀ (ls : List (List Bool)) (ts : List TW) (ss : List SP),
    coverB ls ts ss = true → ∀ l ∈ ls, (∃ t ∈ ts, t.1 = l) ∨ (∃ s ∈ ss, s.1 = l)
  | [], _, _, _, l, hl => by simp at hl
  | l0 :: ls, ts, ss, h, l, hl => by
    match ts, ss with
    | t :: ts', s :: ss' =>
      simp only [coverB] at h
      split_ifs at h with he
      · rw [beq_iff_eq] at he
        rcases List.mem_cons.mp hl with rfl | hl'
        · exact Or.inl ⟨t, by simp, he⟩
        · rcases coverB_sound ls ts' (s :: ss') h l hl' with ⟨t', ht', e⟩ | h2
          · exact Or.inl ⟨t', by simp [ht'], e⟩
          · exact Or.inr h2
      · simp only [Bool.and_eq_true, beq_iff_eq] at h
        rcases List.mem_cons.mp hl with rfl | hl'
        · exact Or.inr ⟨s, by simp, h.1⟩
        · rcases coverB_sound ls (t :: ts') ss' h.2 l hl' with h1 | ⟨s', hs', e⟩
          · exact Or.inl h1
          · exact Or.inr ⟨s', by simp [hs'], e⟩
    | t :: ts', [] =>
      simp only [coverB, Bool.and_eq_true, beq_iff_eq] at h
      rcases List.mem_cons.mp hl with rfl | hl'
      · exact Or.inl ⟨t, by simp, h.1⟩
      · rcases coverB_sound ls ts' [] h.2 l hl' with ⟨t', ht', e⟩ | h2
        · exact Or.inl ⟨t', by simp [ht'], e⟩
        · exact Or.inr h2
    | [], s :: ss' =>
      simp only [coverB, Bool.and_eq_true, beq_iff_eq] at h
      rcases List.mem_cons.mp hl with rfl | hl'
      · exact Or.inr ⟨s, by simp, h.1⟩
      · rcases coverB_sound ls [] ss' h.2 l hl' with h1 | ⟨s', hs', e⟩
        · exact Or.inl h1
        · exact Or.inr ⟨s', by simp [hs'], e⟩
    | [], [] => simp [coverB] at h

/-- Classification from witnesses. -/
theorem classify (n : ℕ) (allQ : List Quad) (cons : ℕ → List Quad) (order : List ℕ)
    (wits : List Wit) (masks : List ℕ)
    (h_check : search cons (fun _ => n) (fun g => masks.contains (bitsVal (parList (2 ^ n) g)))
      order (fun _ => 0) = true)
    (h_masks : masks = wits.map (fun w => bitsVal w.1))
    (h_len : wits.all (fun w => w.1.length == 2 ^ n) = true)
    (h_wf : wfB cons order = true)
    (h_cons : order.all (fun k => (cons k).all fun q => allQ.contains q) = true)
    (h_rel : ∀ q ∈ allQ, q.1 < 2 ^ n ∧ q.2.1 < 2 ^ n ∧ q.2.2.1 < 2 ^ n ∧ q.2.2.2 < 2 ^ n ∧
      Rel (vtx n q.1) (vtx n q.2.1) (vtx n q.2.2.1) (vtx n q.2.2.2))
    (h_fixed : ∀ m < 2 ^ n, m ∉ order → vtx n m = v0 ∨ ∃ i, vtx n m = ve i)
    (h_vtx : ∀ x : Fin n → Bool, vtx n (idx x) = x ∧ idx x < 2 ^ n)
    (h_wit : wits.all (witOk n) = true)
    (h_canon : wits.all (fun w => canonOk n w.1) = true)
    (g : (Fin n → Bool) → Bool) (hg : IsBLF g) (tws : List TW) (sps : List SP)
    (h_tw : tws.all (twOk n) = true) (h_sp : sps.all (spOk n g) = true)
    (h_cov : coverB (wits.map (·.1)) tws sps = true) :
    ∀ f : (Fin n → Bool) → Bool,
      IsBLF f ↔ IsTXA f ∨ ∃ (c : Bool) (b : Fin n → Bool), ∀ x, f x = xor (g x) (affB c b x) := by
  intro f
  have hS := (small_count n allQ cons order wits masks h_check h_masks h_len h_wf h_cons h_rel
    h_fixed h_vtx h_wit h_canon).1
  constructor
  · intro hf
    have hc := (hS f).1 hf
    rw [List.mem_toFinset, List.mem_map] at hc
    obtain ⟨l, hl, hle⟩ := hc
    have := coverB_sound _ _ _ h_cov l hl
    have hfx : ∀ x, f x = xor (canon f x) (affOf f x) := fun x => by simp [canon]
    rcases this with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · left
      rw [List.all_eq_true] at h_tw
      have ho := h_tw t ht
      unfold twOk at ho
      rw [List.all_eq_true] at ho
      refine ⟨t.2.1, fun i => t.2.2.1.getD i.val 0,
        xor t.2.2.2.1 (f v0), fun i => xor (t.2.2.2.2.getD i.val false) (xor (f (ve i)) (f v0)),
        fun x => ?_⟩
      obtain ⟨hv, hlt⟩ := h_vtx x
      have hk := ho (idx x) (List.mem_range.mpr hlt)
      rw [beq_iff_eq] at hk
      rw [hfx x, ← hle]
      simp only [ofList]
      rw [hk, affL_eq _ _ x hv, affOf_eq_affB, hv, Bool.xor_assoc, affB_xor]
      congr 2
    · right
      rw [List.all_eq_true] at h_sp
      have ho := h_sp t ht
      unfold spOk at ho
      rw [List.all_eq_true] at ho
      refine ⟨xor t.2.1 (f v0), fun i => xor (t.2.2.getD i.val false) (xor (f (ve i)) (f v0)),
        fun x => ?_⟩
      obtain ⟨hv, hlt⟩ := h_vtx x
      have hk := ho (idx x) (List.mem_range.mpr hlt)
      rw [beq_iff_eq] at hk
      rw [hfx x, ← hle]
      simp only [ofList]
      rw [hk, affL_eq _ _ x hv, affOf_eq_affB, hv, Bool.xor_assoc, affB_xor]
  · intro hf
    rcases hf with ⟨w0, w, c, b, hf⟩ | ⟨c, b, hf⟩
    · have := (threshold_isBLF' w0 w).xor_aff c b
      have e : f = fun x => xor (decide (0 < w0 + ∑ i, w i * bval (x i))) (aff c b x) := by
        funext x; rw [hf x, aff_eq_affB]
      rw [e]; exact this
    · have e : f = fun x => xor (g x) (aff c b x) := by funext x; rw [hf x, aff_eq_affB]
      rw [e]; exact hg.xor_aff c b

end BLF

module

public import BLF.Search

@[expose] public section

namespace BLF

open Finset

/-- Vertex with code `k` (bit `i` of `k` is coordinate `i`). -/
def vtx (n k : ℕ) : Fin n → Bool := fun i => k.testBit i

/-- Code of a vertex. -/
def idx {n : ℕ} (x : Fin n → Bool) : ℕ := ∑ i, if x i then 2 ^ (i : ℕ) else 0

/-- Boolean function from its truth table (entry `k` is the value at `vtx n k`). -/
def ofList {n : ℕ} (l : List Bool) : (Fin n → Bool) → Bool := fun x => l.getD (idx x) false

lemma idx_v0 {n : ℕ} : idx (v0 : Fin n → Bool) = 0 := by simp [idx, v0]

lemma idx_ve {n : ℕ} (i : Fin n) : idx (ve i) = 2 ^ (i : ℕ) := by
  unfold idx ve
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [hk]
  · simp

/-- `|Gof x| ≤ n`, by induction on the number of true coordinates. -/
lemma abs_Gof_le {n : ℕ} (j : ℕ) (K : ℤ) (a : Fin n → ℤ) :
    ∀ (m : ℕ) (x : Fin n → Bool), (univ.filter fun i => x i = true).card = m →
      |Gof j K a x| ≤ m := by
  intro m
  induction m with
  | zero =>
    intro x hx
    have : x = v0 := by
      funext i; simp only [v0]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hx
      simpa using hx (Finset.mem_univ i)
    subst this; simp [Gof_v0]
  | succ m ih =>
    intro x hx
    obtain ⟨i, hi⟩ : ∃ i, x i = true := by
      by_contra h; push Not at h
      have : (univ.filter fun i => x i = true) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro i _; simp [h i]
      rw [this] at hx; simp at hx
    set x' := Function.update x i false with hx'
    have hc : (univ.filter fun k => x' k = true).card = m := by
      have : (univ.filter fun k => x' k = true) = (univ.filter fun k => x k = true).erase i := by
        ext k; by_cases hk : k = i
        · subst hk; simp [hx']
        · simp [hx', Function.update_of_ne hk, hk]
      rw [this, Finset.card_erase_of_mem (by simp [hi]), hx]; simp
    have hrel : Rel x v0 x' (ve i) := by
      intro k; by_cases hk : k = i
      · subst hk; simp [hx', hi, v0, ve, bval]
      · simp [hx', Function.update_of_ne hk, v0, ve, hk, bval]
    have hp := Gof_par j K a x v0 x' (ve i) hrel
    rw [Gof_v0, Gof_ve] at hp
    have := ih x' hc
    rw [abs_le] at hp this ⊢
    push_cast; constructor <;> linarith

lemma abs_Gof_le_n {n : ℕ} (j : ℕ) (K : ℤ) (a : Fin n → ℤ) (x : Fin n → Bool) :
    |Gof j K a x| ≤ n := by
  have h := abs_Gof_le j K a _ x rfl
  have : ((univ.filter fun i => x i = true).card : ℤ) ≤ n := by
    have := Finset.card_filter_le (univ : Finset (Fin n)) (fun i => x i = true)
    simp at this; exact_mod_cast this
  linarith

/-- Sharper bound: `|Gof x| ≤ m` when `x` has `m + 1` true coordinates. -/
lemma abs_Gof_le_pred {n : ℕ} (j : ℕ) (K : ℤ) (a : Fin n → ℤ) :
    ∀ (m : ℕ) (x : Fin n → Bool), (univ.filter fun i => x i = true).card = m + 1 →
      |Gof j K a x| ≤ m := by
  intro m
  induction m with
  | zero =>
    intro x hx
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hx
    have : x = ve i := by
      funext k
      have hk := congrArg (k ∈ ·) hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hk
      simp only [ve]
      cases hxk : x k <;> simp_all
    subst this; simp [Gof_ve]
  | succ m ih =>
    intro x hx
    obtain ⟨i, hi⟩ : ∃ i, x i = true := by
      by_contra h; push Not at h
      have : (univ.filter fun i => x i = true) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro i _; simp [h i]
      rw [this] at hx; simp at hx
    set x' := Function.update x i false with hx'
    have hc : (univ.filter fun k => x' k = true).card = m + 1 := by
      have : (univ.filter fun k => x' k = true) = (univ.filter fun k => x k = true).erase i := by
        ext k; by_cases hk : k = i
        · subst hk; simp [hx']
        · simp [hx', hk]
      rw [this, Finset.card_erase_of_mem (by simp [hi]), hx]; simp
    have hrel : Rel x v0 x' (ve i) := by
      intro k; by_cases hk : k = i
      · subst hk; simp [hx', hi, v0, ve, bval]
      · simp [hx', v0, ve, hk, bval]
    have hp := Gof_par j K a x v0 x' (ve i) hrel
    rw [Gof_v0, Gof_ve] at hp
    have := ih x' hc
    rw [abs_le] at hp this ⊢
    push_cast; constructor <;> linarith

/-- Truth table of the parities of `g` on codes `0, ..., N-1`. -/
def parList (N : ℕ) (g : ℕ → ℤ) : List Bool := (List.range N).map fun k => decide (g k % 2 = 1)

/-- A truth table read as a binary number (entry 0 is the lowest bit). -/
def bitsVal : List Bool → ℕ
  | [] => 0
  | b :: l => (if b then 1 else 0) + 2 * bitsVal l

lemma bitsVal_inj : ∀ (l1 l2 : List Bool), l1.length = l2.length → bitsVal l1 = bitsVal l2 → l1 = l2
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | b1 :: l1, b2 :: l2, h, hv => by
    simp only [bitsVal] at hv
    have hb : b1 = b2 := by cases b1 <;> cases b2 <;> simp at hv ⊢ <;> omega
    subst hb
    have : bitsVal l1 = bitsVal l2 := by cases b1 <;> simp at hv <;> omega
    rw [bitsVal_inj l1 l2 (by simpa using h) this]

/-- Witness record: truth table, bit position, constant, coefficients. -/
abbrev Wit := List Bool × ℕ × ℤ × List ℤ

def witOk (n : ℕ) (w : Wit) : Bool :=
  (List.range (2 ^ n)).all fun k => w.1.getD k false ==
    bitAt w.2.1 (w.2.2.1 + ((List.finRange n).map fun i : Fin n => w.2.2.2.getD i.val 0 * bval (vtx n k i)).sum)

def canonOk (n : ℕ) (l : List Bool) : Bool :=
  !(l.getD 0 false) && (List.range n).all fun i => !(l.getD (2 ^ i) false)

/-- Exact characterization and count from finite data checked by computation. -/
theorem small_count (n : ℕ) (allQ : List Quad) (cons : ℕ → List Quad) (order : List ℕ)
    (wits : List Wit) (bnd : ℕ → ℕ)
    (masks : List ℕ)
    (h_check : search cons bnd (fun g => masks.contains (bitsVal (parList (2 ^ n) g)))
      order (fun _ => 0) = true)
    (h_bnd : ∀ k ∈ order, (univ.filter fun i : Fin n => vtx n k i = true).card = bnd k + 1)
    (h_masks : masks = wits.map (fun w => bitsVal w.1))
    (h_len : wits.all (fun w => w.1.length == 2 ^ n) = true)
    (h_wf : wfB cons order = true)
    (h_cons : order.all (fun k => (cons k).all fun q => allQ.contains q) = true)
    (h_rel : ∀ q ∈ allQ, q.1 < 2 ^ n ∧ q.2.1 < 2 ^ n ∧ q.2.2.1 < 2 ^ n ∧ q.2.2.2 < 2 ^ n ∧
      Rel (vtx n q.1) (vtx n q.2.1) (vtx n q.2.2.1) (vtx n q.2.2.2))
    (h_fixed : ∀ m < 2 ^ n, m ∉ order → vtx n m = v0 ∨ ∃ i, vtx n m = ve i)
    (h_vtx : ∀ x : Fin n → Bool, vtx n (idx x) = x ∧ idx x < 2 ^ n)
    (h_wit : wits.all (witOk n) = true)
    (h_canon : wits.all (fun w => canonOk n w.1) = true) :
    (∀ f : (Fin n → Bool) → Bool,
      IsBLF f ↔ canon f ∈ ((wits.map (·.1)).map (ofList (n := n))).toFinset) ∧
    Nat.card {f : (Fin n → Bool) → Bool // IsBLF f} =
      (((wits.map (·.1)).map (ofList (n := n))).toFinset).card * (2 * 2 ^ n) := by
  classical
  set S := ((wits.map (·.1)).map (ofList (n := n))).toFinset with hSdef
  have hiff : ∀ f : (Fin n → Bool) → Bool, IsBLF f ↔ canon f ∈ S := by
    intro f
    constructor
    · rintro ⟨j, K, a, hf⟩
      set G' : ℕ → ℤ := fun k => if k < 2 ^ n then Gof j K a (vtx n k) else 0 with hG'
      have hleaf := search_sound cons bnd
        (fun g => masks.contains (bitsVal (parList (2 ^ n) g))) order (fun _ => 0) G' h_check h_wf
        (by
          intro m hm
          by_cases hlt : m < 2 ^ n
          · simp only [hG', hlt, ite_true]
            rcases h_fixed m hlt hm with h | ⟨i, h⟩
            · rw [h, Gof_v0]
            · rw [h, Gof_ve]
          · simp [hG', hlt])
        (by
          intro k hk
          simp only [hG']
          split_ifs
          · exact abs_Gof_le_pred j K a _ _ (h_bnd k hk)
          · simp)
        (by
          intro k hk
          rw [List.all_eq_true] at h_cons
          have hk' := h_cons k hk
          rw [List.all_eq_true] at hk' ⊢
          intro q hq
          have hqA : q ∈ allQ := by simpa using hk' q hq
          obtain ⟨l1, l2, l3, l4, hr⟩ := h_rel q hqA
          apply okQ_of_abs
          simp only [hG', l1, l2, l3, l4, ite_true]
          exact Gof_par j K a _ _ _ _ hr)
      have hmem : parList (2 ^ n) G' ∈ wits.map (·.1) := by
        rw [h_masks] at hleaf
        simp only [List.contains_iff_mem, List.mem_map] at hleaf
        obtain ⟨w, hw, hv⟩ := hleaf
        rw [List.all_eq_true] at h_len
        have hl := h_len w hw
        rw [beq_iff_eq] at hl
        have := bitsVal_inj w.1 (parList (2 ^ n) G') (by simp [parList, hl]) hv
        exact List.mem_map.mpr ⟨w, hw, this⟩
      have hcf : canon f = ofList (parList (2 ^ n) G') := by
        rw [canon_eq_Gof j K a f hf]
        funext x
        obtain ⟨hv, hlt⟩ := h_vtx x
        simp only [ofList, parList]
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]
        simp only [Option.map_some, Option.getD_some, hG', hlt, ite_true, hv]
        rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, odd_iff_par]
      rw [hcf, hSdef, List.mem_toFinset]
      exact List.mem_map.mpr ⟨_, hmem, rfl⟩
    · intro hc
      rw [hSdef, List.mem_toFinset, List.mem_map] at hc
      obtain ⟨l, hl, hle⟩ := hc
      rw [List.mem_map] at hl
      obtain ⟨w, hw, rfl⟩ := hl
      rw [isBLF_iff_canon, ← hle]
      rw [List.all_eq_true] at h_wit
      have hwo := h_wit w hw
      refine ⟨w.2.1, w.2.2.1, fun i => w.2.2.2.getD i.val 0, fun x => ?_⟩
      obtain ⟨hv, hlt⟩ := h_vtx x
      unfold witOk at hwo
      rw [List.all_eq_true] at hwo
      have hk := hwo (idx x) (List.mem_range.mpr hlt)
      rw [beq_iff_eq, hv] at hk
      simp only [ofList]
      rw [hk]
      congr 1
  refine ⟨hiff, card_of_canon S ?_ IsBLF hiff⟩
  intro s hs
  rw [hSdef, List.mem_toFinset, List.mem_map] at hs
  obtain ⟨l, hl, rfl⟩ := hs
  rw [List.mem_map] at hl
  obtain ⟨w, hw, rfl⟩ := hl
  rw [List.all_eq_true] at h_canon
  have hc := h_canon w hw
  unfold canonOk at hc
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hc
  obtain ⟨h0, hi⟩ := hc
  refine ⟨?_, fun i => ?_⟩
  · simp only [ofList, idx_v0]; exact h0
  · simp only [ofList, idx_ve]
    have := hi i.val (List.mem_range.mpr i.isLt)
    simpa using this

end BLF

namespace BLF

/-- The class set has as many elements as there are witnesses, when the truth tables are
pairwise distinct (checked on their binary values) and of full length. -/
theorem card_classes (n : ℕ) (wits : List Wit)
    (h_len : wits.all (fun w => w.1.length == 2 ^ n) = true)
    (h_idx : ∀ k < 2 ^ n, idx (vtx n k) = k)
    (h_nd : (wits.map (fun w => bitsVal w.1)).Nodup) :
    (((wits.map (·.1)).map (ofList (n := n))).toFinset).card = wits.length := by
  have hmap : wits.map (fun w => bitsVal w.1) = (wits.map (·.1)).map bitsVal := by
    simp [List.map_map, Function.comp_def]
  rw [hmap] at h_nd
  have nd1 : (wits.map (·.1)).Nodup := h_nd.of_map _
  have hl : ∀ l ∈ wits.map (·.1), l.length = 2 ^ n := by
    intro l hl
    rw [List.mem_map] at hl
    obtain ⟨w, hw, rfl⟩ := hl
    rw [List.all_eq_true] at h_len
    simpa using h_len w hw
  have inj : ∀ l1 ∈ wits.map (·.1), ∀ l2 ∈ wits.map (·.1),
      ofList (n := n) l1 = ofList (n := n) l2 → l1 = l2 := by
    intro l1 h1 l2 h2 he
    apply List.ext_getElem (by rw [hl l1 h1, hl l2 h2])
    intro k hk1 hk2
    have hk : k < 2 ^ n := by rw [← hl l1 h1]; exact hk1
    have := congrFun he (vtx n k)
    simp only [ofList, h_idx k hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk1,
      List.getElem?_eq_getElem hk2, Option.getD_some] at this
    exact this
  rw [List.toFinset_card_of_nodup (nd1.map_on inj), List.length_map, List.length_map]

end BLF

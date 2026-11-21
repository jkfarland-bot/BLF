module

public import BLF.Affine

@[expose] public section

namespace BLF

open Finset

/-- The zero vertex and the unit vertices. -/
def v0 {n : ℕ} : Fin n → Bool := fun _ => false
def ve {n : ℕ} (i : Fin n) : Fin n → Bool := fun k => decide (k = i)

lemma affZ_v0 {n : ℕ} (c : Bool) (b : Fin n → Bool) : affZ c b v0 = par (bval c) := by
  simp [affZ, v0, bval, par]

lemma affZ_ve {n : ℕ} (c : Bool) (b : Fin n → Bool) (i : Fin n) :
    affZ c b (ve i) = par (bval c) + par (bval (b i)) := by
  unfold affZ ve
  congr 1
  rw [Finset.sum_eq_single i]
  · simp [bval, par]
  · intro k _ hk; simp [hk, bval, par]
  · simp

lemma aff_v0 {n : ℕ} (c : Bool) (b : Fin n → Bool) : aff c b v0 = c := by
  unfold aff; rw [affZ_v0]; cases c <;> simp [bval, par]

lemma aff_ve {n : ℕ} (c : Bool) (b : Fin n → Bool) (i : Fin n) : aff c b (ve i) = xor c (b i) := by
  unfold aff; rw [affZ_ve]; cases c <;> cases b i <;> simp [bval, par]

/-- The affine function that agrees with `f` at `0` and at each `e_i`. -/
def affOf {n : ℕ} (f : (Fin n → Bool) → Bool) : (Fin n → Bool) → Bool :=
  aff (f v0) (fun i => xor (f (ve i)) (f v0))

/-- Canonical representative of the output-affine class of `f`: `f XOR affOf f`. -/
def canon {n : ℕ} (f : (Fin n → Bool) → Bool) : (Fin n → Bool) → Bool :=
  fun x => xor (f x) (affOf f x)

/-- `g` is canonical: it vanishes at `0` and at every `e_i`. -/
def IsCanon {n : ℕ} (g : (Fin n → Bool) → Bool) : Prop := g v0 = false ∧ ∀ i, g (ve i) = false

lemma affOf_aff {n : ℕ} (c : Bool) (b : Fin n → Bool) : affOf (aff c b) = aff c b := by
  unfold affOf
  congr 1
  · exact aff_v0 c b
  · funext i; rw [aff_ve, aff_v0]; cases c <;> cases b i <;> rfl

lemma affOf_xor {n : ℕ} (s : (Fin n → Bool) → Bool) (hs : IsCanon s) (c : Bool)
    (b : Fin n → Bool) : affOf (fun x => xor (s x) (aff c b x)) = aff c b := by
  unfold affOf
  simp only [hs.1, hs.2, Bool.false_xor]
  exact affOf_aff c b

lemma canon_xor {n : ℕ} (s : (Fin n → Bool) → Bool) (hs : IsCanon s) (c : Bool)
    (b : Fin n → Bool) : canon (fun x => xor (s x) (aff c b x)) = s := by
  unfold canon; rw [affOf_xor s hs]; funext x; simp

lemma xor_canon {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (fun x => xor (canon f x) (affOf f x)) = f := by
  funext x; simp [canon]

lemma canon_isCanon {n : ℕ} (f : (Fin n → Bool) → Bool) : IsCanon (canon f) := by
  refine ⟨?_, fun i => ?_⟩
  · simp [canon, affOf, aff_v0]
  · simp only [canon, affOf, aff_ve]; cases f v0 <;> cases f (ve i) <;> rfl

/-- **Counting.** If `P f ↔ canon f ∈ S` with every element of `S` canonical, then exactly
`|S| * 2^(n+1)` functions satisfy `P`. -/
theorem card_of_canon {n : ℕ} (S : Finset ((Fin n → Bool) → Bool)) (hS : ∀ s ∈ S, IsCanon s)
    (P : ((Fin n → Bool) → Bool) → Prop) (hP : ∀ f, P f ↔ canon f ∈ S) :
    Nat.card {f // P f} = S.card * (2 * 2 ^ n) := by
  classical
  have e : {f // P f} ≃ S × (Bool × (Fin n → Bool)) :=
    { toFun := fun f => (⟨canon f.1, (hP f.1).1 f.2⟩, (f.1 v0, fun i => xor (f.1 (ve i)) (f.1 v0)))
      invFun := fun p => ⟨fun x => xor (p.1.1 x) (aff p.2.1 p.2.2 x), by
        rw [hP, canon_xor _ (hS _ p.1.2)]; exact p.1.2⟩
      left_inv := by
        rintro ⟨f, hf⟩
        apply Subtype.ext
        exact xor_canon f
      right_inv := by
        rintro ⟨⟨s, hs⟩, c, b⟩
        have hc := hS s hs
        simp only [Prod.mk.injEq, Subtype.mk.injEq]
        refine ⟨canon_xor s hc c b, ?_, ?_⟩
        · simp [hc.1, aff_v0]
        · funext i; simp only [hc.1, hc.2, aff_v0, aff_ve, Bool.false_xor]
          cases c <;> cases b i <;> rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_coe, Fintype.card_bool, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- BLF is a union of output-affine classes: `IsBLF f ↔ IsBLF (canon f)`. -/
lemma isBLF_iff_canon {n : ℕ} (f : (Fin n → Bool) → Bool) : IsBLF f ↔ IsBLF (canon f) := by
  constructor
  · intro h; exact h.xor_aff _ _
  · intro h
    have := h.xor_aff (f v0) (fun i => xor (f (ve i)) (f v0))
    rwa [show (fun x => xor (canon f x) (aff (f v0) (fun i => xor (f (ve i)) (f v0)) x)) = f
      from xor_canon f] at this

end BLF

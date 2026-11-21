module

public import BLF.Data1

@[expose] public section

namespace BLF
namespace N1

def masks : List ℕ := wits.map (fun w => bitsVal w.1)
theorem check : search cons bnd (fun g => masks.contains (bitsVal (parList (2 ^ 1) g)))
    order (fun _ => 0) = true := by decide +kernel
theorem lenOk : wits.all (fun w => w.1.length == 2 ^ 1) = true := by decide +kernel
theorem wf : wfB cons order = true := by decide +kernel
theorem bndOk : ∀ k ∈ order, (Finset.univ.filter fun i : Fin 1 => vtx 1 k i = true).card = bnd k + 1 := by
  decide +kernel
theorem consOk : order.all (fun k => (cons k).all fun q => allQ.contains q) = true := by decide +kernel
theorem relOk : ∀ q ∈ allQ, q.1 < 2 ^ 1 ∧ q.2.1 < 2 ^ 1 ∧ q.2.2.1 < 2 ^ 1 ∧ q.2.2.2 < 2 ^ 1 ∧
    Rel (vtx 1 q.1) (vtx 1 q.2.1) (vtx 1 q.2.2.1) (vtx 1 q.2.2.2) := by
  unfold Rel; decide +kernel
theorem fixedOk : ∀ m < 2 ^ 1, m ∉ order → vtx 1 m = v0 ∨ ∃ i, vtx 1 m = ve i := by decide +kernel
theorem vtxOk : ∀ x : Fin 1 → Bool, vtx 1 (idx x) = x ∧ idx x < 2 ^ 1 := by decide +kernel
theorem witOk' : wits.all (witOk 1) = true := by decide +kernel
theorem canonOk' : wits.all (fun w => canonOk 1 w.1) = true := by decide +kernel
theorem idxOk : ∀ k < 2 ^ 1, idx (vtx 1 k) = k := by decide +kernel
theorem nodupOk : (wits.map (fun w => bitsVal w.1)).Nodup := by decide +kernel
theorem cardS : (((wits.map (·.1)).map (ofList (n := 1))).toFinset).card = 1 := by
  rw [card_classes 1 wits lenOk idxOk nodupOk]; decide +kernel

end N1
end BLF

namespace BLF

/-- **|BLF(1)| = 4.** -/
theorem card_blf_one : Nat.card {f : (Fin 1 → Bool) → Bool // IsBLF f} = 4 := by
  rw [(small_count 1 N1.allQ N1.cons N1.order N1.wits N1.bnd N1.masks N1.check N1.bndOk rfl N1.lenOk N1.wf N1.consOk N1.relOk
    N1.fixedOk N1.vtxOk N1.witOk' N1.canonOk').2, N1.cardS]
  norm_num

end BLF

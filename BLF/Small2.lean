module

public import BLF.Data2

@[expose] public section

namespace BLF
namespace N2

def masks : List ℕ := wits.map (fun w => bitsVal w.1)
theorem check : search cons bnd (fun g => masks.contains (bitsVal (parList (2 ^ 2) g)))
    order (fun _ => 0) = true := by decide +kernel
theorem lenOk : wits.all (fun w => w.1.length == 2 ^ 2) = true := by decide +kernel
theorem wf : wfB cons order = true := by decide +kernel
theorem bndOk : ∀ k ∈ order, (Finset.univ.filter fun i : Fin 2 => vtx 2 k i = true).card = bnd k + 1 := by
  decide +kernel
theorem consOk : order.all (fun k => (cons k).all fun q => allQ.contains q) = true := by decide +kernel
theorem relOk : ∀ q ∈ allQ, q.1 < 2 ^ 2 ∧ q.2.1 < 2 ^ 2 ∧ q.2.2.1 < 2 ^ 2 ∧ q.2.2.2 < 2 ^ 2 ∧
    Rel (vtx 2 q.1) (vtx 2 q.2.1) (vtx 2 q.2.2.1) (vtx 2 q.2.2.2) := by
  unfold Rel; decide +kernel
theorem fixedOk : ∀ m < 2 ^ 2, m ∉ order → vtx 2 m = v0 ∨ ∃ i, vtx 2 m = ve i := by decide +kernel
theorem vtxOk : ∀ x : Fin 2 → Bool, vtx 2 (idx x) = x ∧ idx x < 2 ^ 2 := by decide +kernel
theorem witOk' : wits.all (witOk 2) = true := by decide +kernel
theorem canonOk' : wits.all (fun w => canonOk 2 w.1) = true := by decide +kernel
theorem idxOk : ∀ k < 2 ^ 2, idx (vtx 2 k) = k := by decide +kernel
theorem nodupOk : (wits.map (fun w => bitsVal w.1)).Nodup := by decide +kernel
theorem cardS : (((wits.map (·.1)).map (ofList (n := 2))).toFinset).card = 2 := by
  rw [card_classes 2 wits lenOk idxOk nodupOk]; decide +kernel

end N2
end BLF

namespace BLF

/-- **|BLF(2)| = 16.** -/
theorem card_blf_two : Nat.card {f : (Fin 2 → Bool) → Bool // IsBLF f} = 16 := by
  rw [(small_count 2 N2.allQ N2.cons N2.order N2.wits N2.bnd N2.masks N2.check N2.bndOk rfl N2.lenOk N2.wf N2.consOk N2.relOk
    N2.fixedOk N2.vtxOk N2.witOk' N2.canonOk').2, N2.cardS]
  norm_num

end BLF

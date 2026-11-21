module

public import BLF.Check4

@[expose] public section

namespace BLF
namespace N4

theorem lenOk : wits.all (fun w => w.1.length == 2 ^ 4) = true := by decide +kernel
theorem wf : wfB cons order = true := by decide +kernel
theorem bndOk : ∀ k ∈ order, (Finset.univ.filter fun i : Fin 4 => vtx 4 k i = true).card = bnd k + 1 := by
  decide +kernel
theorem consOk : order.all (fun k => (cons k).all fun q => allQ.contains q) = true := by decide +kernel
theorem relOk : ∀ q ∈ allQ, q.1 < 2 ^ 4 ∧ q.2.1 < 2 ^ 4 ∧ q.2.2.1 < 2 ^ 4 ∧ q.2.2.2 < 2 ^ 4 ∧
    Rel (vtx 4 q.1) (vtx 4 q.2.1) (vtx 4 q.2.2.1) (vtx 4 q.2.2.2) := by
  unfold Rel; decide +kernel
theorem fixedOk : ∀ m < 2 ^ 4, m ∉ order → vtx 4 m = v0 ∨ ∃ i, vtx 4 m = ve i := by decide +kernel
theorem vtxOk : ∀ x : Fin 4 → Bool, vtx 4 (idx x) = x ∧ idx x < 2 ^ 4 := by decide +kernel
theorem witOk' : wits.all (witOk 4) = true := by decide +kernel
theorem canonOk' : wits.all (fun w => canonOk 4 w.1) = true := by decide +kernel
theorem idxOk : ∀ k < 2 ^ 4, idx (vtx 4 k) = k := by decide +kernel
theorem nodupOk : (wits.map (fun w => bitsVal w.1)).Nodup := by decide +kernel
theorem cardS : (((wits.map (·.1)).map (ofList (n := 4))).toFinset).card = 324 := by
  rw [card_classes 4 wits lenOk idxOk nodupOk]; decide +kernel

end N4
end BLF

namespace BLF

/-- **|BLF(4)| = 10,368.** -/
theorem card_blf_four : Nat.card {f : (Fin 4 → Bool) → Bool // IsBLF f} = 10368 := by
  rw [(small_count 4 N4.allQ N4.cons N4.order N4.wits N4.bnd N4.masks N4.check N4.bndOk rfl N4.lenOk N4.wf N4.consOk N4.relOk
    N4.fixedOk N4.vtxOk N4.witOk' N4.canonOk').2, N4.cardS]
  norm_num

end BLF

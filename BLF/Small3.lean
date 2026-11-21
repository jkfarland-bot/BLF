import BLF.Data3

namespace BLF
namespace N3

def masks : List ℕ := wits.map (fun w => bitsVal w.1)
theorem check : search cons (fun _ => 3) (fun g => masks.contains (bitsVal (parList (2 ^ 3) g)))
    order (fun _ => 0) = true := by decide +kernel
theorem lenOk : wits.all (fun w => w.1.length == 2 ^ 3) = true := by decide +kernel
theorem wf : wfB cons order = true := by decide +kernel
theorem consOk : order.all (fun k => (cons k).all fun q => allQ.contains q) = true := by decide +kernel
theorem relOk : ∀ q ∈ allQ, q.1 < 2 ^ 3 ∧ q.2.1 < 2 ^ 3 ∧ q.2.2.1 < 2 ^ 3 ∧ q.2.2.2 < 2 ^ 3 ∧
    Rel (vtx 3 q.1) (vtx 3 q.2.1) (vtx 3 q.2.2.1) (vtx 3 q.2.2.2) := by
  unfold Rel; decide +kernel
theorem fixedOk : ∀ m < 2 ^ 3, m ∉ order → vtx 3 m = v0 ∨ ∃ i, vtx 3 m = ve i := by decide +kernel
theorem vtxOk : ∀ x : Fin 3 → Bool, vtx 3 (idx x) = x ∧ idx x < 2 ^ 3 := by decide +kernel
theorem witOk' : wits.all (witOk 3) = true := by decide +kernel
theorem canonOk' : wits.all (fun w => canonOk 3 w.1) = true := by decide +kernel
theorem cardS : (((wits.map (·.1)).map (ofList (n := 3))).toFinset).card = 13 := by decide +kernel

end N3
end BLF

namespace BLF

/-- **|BLF(3)| = 208.** -/
theorem card_blf_three : Nat.card {f : (Fin 3 → Bool) → Bool // IsBLF f} = 208 := by
  rw [(small_count 3 N3.allQ N3.cons N3.order N3.wits N3.masks N3.check rfl N3.lenOk N3.wf N3.consOk N3.relOk
    N3.fixedOk N3.vtxOk N3.witOk' N3.canonOk').2, N3.cardS]
  norm_num

end BLF

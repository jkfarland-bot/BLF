module

public import BLF.TxaData3

@[expose] public section

namespace BLF
namespace N3

theorem spOk' : sps.all (spOk 3 (fun _ => false)) = true := by decide +kernel
theorem covOk : coverB (wits.map (·.1)) tws sps = true := by decide +kernel

end N3

/-- For three variables, BLF is exactly threshold XOR affine. -/
theorem blf_three_iff_txa' (f : (Fin 3 → Bool) → Bool) : IsBLF f ↔ IsTXA f := by
  have hg : IsBLF (fun _ : Fin 3 → Bool => false) := ⟨0, 0, fun _ => 0, fun x => by simp [bitAt, lin]⟩
  rw [classify 3 N3.allQ N3.cons N3.order N3.wits N3.bnd N3.masks N3.check N3.bndOk rfl N3.lenOk N3.wf N3.consOk
    N3.relOk N3.fixedOk N3.vtxOk N3.witOk' N3.canonOk' _ hg N3.tws N3.sps N3.twOk' N3.spOk'
    N3.covOk f]
  constructor
  · rintro (h | ⟨c, b, h⟩)
    · exact h
    · exact ⟨0, fun _ => 0, c, b, fun x => by rw [h x]; simp⟩
  · exact Or.inl

end BLF

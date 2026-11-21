module

public import BLF.TxaData4

@[expose] public section

namespace BLF

/-- Bit 1 of `x_1 + x_2 + x_3 + x_4`. -/
def bitOneSum (x : Fin 4 → Bool) : Bool := bitAt 1 (∑ i, bval (x i))

namespace N4

theorem spOk' : sps.all (spOk 4 bitOneSum) = true := by decide +kernel
theorem covOk : coverB (wits.map (·.1)) tws sps = true := by decide +kernel

end N4

lemma bitOneSum_isBLF : IsBLF bitOneSum := ⟨1, 0, fun _ => 1, fun x => by simp [bitOneSum, lin]⟩

/-- For four variables, BLF is threshold XOR affine together with the affine translates of
bit 1 of `x_1 + x_2 + x_3 + x_4`. -/
theorem blf_four_iff' (f : (Fin 4 → Bool) → Bool) :
    IsBLF f ↔ IsTXA f ∨ ∃ (c : Bool) (b : Fin 4 → Bool), ∀ x, f x = xor (bitOneSum x) (affB c b x) :=
  classify 4 N4.allQ N4.cons N4.order N4.wits N4.bnd N4.masks N4.check N4.bndOk rfl N4.lenOk N4.wf N4.consOk
    N4.relOk N4.fixedOk N4.vtxOk N4.witOk' N4.canonOk' _ bitOneSum_isBLF N4.tws N4.sps N4.twOk'
    N4.spOk' N4.covOk f

end BLF

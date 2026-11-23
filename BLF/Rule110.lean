module

public import BLF.Square

@[expose] public section

/-!
# Two and three steps of Rule 110 are not BLF

On the square of the last two inputs, the patterns `0,1,1,1` (base `0`) and `0,1,0,0` (base with the
second cell, respectively the third cell, set) need opposite parities in the square identity.
-/

namespace BLF

theorem rule110Two_not_isBLF' : ¬ IsBLF rule110Two := by
  intro hf
  obtain ⟨βi, βk, h⟩ := square_parity hf 3 4 (by decide)
  have h1 := h ![false, false, false, false, false] rfl rfl
  have h2 := h ![false, true, false, false, false] rfl rfl
  revert h1 h2
  revert βi βk
  decide +kernel

theorem rule110Three_not_isBLF' : ¬ IsBLF rule110Three := by
  intro hf
  obtain ⟨βi, βk, h⟩ := square_parity hf 5 6 (by decide)
  have h1 := h ![false, false, false, false, false, false, false] rfl rfl
  have h2 := h ![false, false, true, false, false, false, false] rfl rfl
  revert h1 h2
  revert βi βk
  decide +kernel

end BLF

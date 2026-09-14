import Mathlib

namespace Commons.FieldTheory.Galois

theorem algHom_fieldRange_eq_adjoin_image {L : Type*} [Field L] [Algebra ℚ L] (ψ : L →ₐ[ℚ] ℂ)
    (s : Set L) (h : IntermediateField.adjoin ℚ s = ⊤) :
    ψ.fieldRange = IntermediateField.adjoin ℚ (ψ '' s) := by
  rw [AlgHom.fieldRange_eq_map, ← h, IntermediateField.adjoin_map]

end Commons.FieldTheory.Galois

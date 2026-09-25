import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.NumberField.Basic

namespace Commons.NumberTheory.NumberField

theorem numberField_of_intermediateField {K K' : Type*} [Field K] [NumberField K] [Field K']
    [Algebra K K'] (L : IntermediateField K K') [FiniteDimensional K L] : NumberField ↥L := by
  have h : FiniteDimensional ℚ ↥L := FiniteDimensional.trans ℚ K ↥L
  exact NumberField.mk (to_charZero := inferInstance) (to_finiteDimensional := h)

end Commons.NumberTheory.NumberField
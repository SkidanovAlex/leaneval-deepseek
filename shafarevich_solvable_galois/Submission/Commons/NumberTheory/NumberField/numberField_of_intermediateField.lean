import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.NumberField.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField

theorem numberField_of_intermediateField {K K' : Type*} [Field K] [NumberField K] [Field K']
    [Algebra K K'] (L : IntermediateField K K') [FiniteDimensional K L] : NumberField ↥L := by
  have h : FiniteDimensional ℚ ↥L := FiniteDimensional.trans ℚ K ↥L
  exact NumberField.mk (to_charZero := inferInstance) (to_finiteDimensional := h)

end Commons.NumberTheory.NumberField
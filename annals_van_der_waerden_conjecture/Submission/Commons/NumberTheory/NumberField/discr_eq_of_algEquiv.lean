import Mathlib.NumberTheory.NumberField.Discriminant.Defs

namespace Commons.NumberTheory.NumberField

theorem discr_eq_of_algEquiv {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra ℚ K] [Algebra ℚ L] (e : K ≃ₐ[ℚ] L) :
    NumberField.discr K = NumberField.discr L := by
  exact NumberField.discr_eq_discr_of_ringEquiv K (e : K ≃+* L)

end Commons.NumberTheory.NumberField
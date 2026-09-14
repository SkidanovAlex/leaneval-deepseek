import Mathlib.NumberTheory.NumberField.Basic

open NumberField

namespace Commons.NumberTheory.NumberField

/-- The splitting field of a nonzero polynomial over a number field is again a number field. -/
theorem splittingField_numberField {K : Type} [Field K] [NumberField K] {f : Polynomial K}
    (hf : f ≠ 0) : NumberField (Polynomial.SplittingField f) := by
  exact NumberField.of_module_finite K (Polynomial.SplittingField f)

end Commons.NumberTheory.NumberField
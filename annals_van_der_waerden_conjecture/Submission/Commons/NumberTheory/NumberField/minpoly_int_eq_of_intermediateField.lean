import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Minpoly.Basic

namespace Commons.NumberTheory.NumberField

/-- The minimal polynomial over `ℤ` of an element of an intermediate field `ℚ ≤ K ≤ ℂ`
does not depend on whether it is computed inside `K` or inside the ambient field `ℂ`.

This is a special case of `minpoly.algebraMap_eq`, applied to the injective `ℤ`-algebra
map `↥K → ℂ` (which is the coercion, i.e. `IntermediateField.val K`). -/
theorem minpoly_int_eq_of_intermediateField {K : IntermediateField ℚ ℂ} (z : ↥K) :
    minpoly ℤ (z : ℂ) = minpoly ℤ z := by
  have hinj : Function.Injective (algebraMap ↥K ℂ) := (IntermediateField.val K).injective
  have h := minpoly.algebraMap_eq (A := ℤ) (B := ↥K) (B' := ℂ) hinj z
  simpa using h

end Commons.NumberTheory.NumberField
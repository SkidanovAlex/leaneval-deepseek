import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Minpoly.Basic

namespace Commons.NumberTheory.NumberField

theorem isIntegral_map_of_isIntegral {K : Type*} [Field K] [Algebra ℚ K]
    (ψ : K →ₐ[ℚ] ℂ) {x : K} (hx : IsIntegral ℤ x) : IsIntegral ℤ (ψ x) := by
  exact IsIntegral.map ψ hx

end Commons.NumberTheory.NumberField
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Commons.Measure.Real

set_option autoImplicit false

/-- `r ↦ (1 + r²)⁻¹` is integrable on `(0, ∞)`. -/
theorem integrableOn_one_add_sq_inv_Ioi :
    MeasureTheory.IntegrableOn (fun r : ℝ => (1 + r ^ 2)⁻¹) (Set.Ioi (0 : ℝ))
      MeasureTheory.volume :=
  integrable_inv_one_add_sq.integrableOn

end Commons.Measure.Real
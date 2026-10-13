import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Auxiliary

/-- The inner product against a fixed vector `c` commutes with the Bochner integral: the map
`y ↦ ⟪c, y⟫` is a continuous linear functional (`innerSL ℝ c`), and for such a functional the
integral of the composition is the composition with the integral, provided the integrand is
integrable — here `ψ` is continuous with compact support.

This is the linearity of the Bochner integral against a continuous linear functional, recorded
as a standalone lemma for the pressure construction. -/
theorem integral_inner_eq_inner_integral (c : EuclideanSpace ℝ (Fin 3))
    (ψ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, inner ℝ c (ψ x) = inner ℝ c (∫ x, ψ x) := by
  have hint : MeasureTheory.Integrable ψ := hψ.integrable_of_hasCompactSupport hψc
  have h := ContinuousLinearMap.integral_comp_comm (innerSL ℝ c) hint
  simpa using h

end Work.FTS.PressureOn.Auxiliary

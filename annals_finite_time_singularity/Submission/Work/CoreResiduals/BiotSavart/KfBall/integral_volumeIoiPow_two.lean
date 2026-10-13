import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Constructions.HaarToSphere

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

namespace Work.CoreResiduals.BiotSavart.KfBall

/-- Integrating against the radial measure `Measure.volumeIoiPow 2` on `(0,∞)`
(whose density with respect to Lebesgue measure is `r ↦ r²`) is the same as
integrating `r ↦ r² • F r` against Lebesgue measure restricted to `(0,∞)`. -/
theorem integral_volumeIoiPow_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ → E) :
    ∫ r : Set.Ioi (0 : ℝ), F (r : ℝ) ∂(MeasureTheory.Measure.volumeIoiPow 2)
      = ∫ r in Set.Ioi (0 : ℝ), r ^ 2 • F r := by
  rw [Measure.volumeIoiPow,
    integral_withDensity_eq_integral_toReal_smul (f := fun r : Set.Ioi (0:ℝ) => ENNReal.ofReal ((r:ℝ)^2))
      (by fun_prop) (Filter.Eventually.of_forall (fun r => ENNReal.ofReal_lt_top))]
  have : ∀ r : Set.Ioi (0:ℝ), (ENNReal.ofReal ((r:ℝ)^2)).toReal • F (r:ℝ) = (r:ℝ)^2 • F (r:ℝ) :=
    fun r => by rw [ENNReal.toReal_ofReal (sq_nonneg _)]
  simp_rw [this]
  exact integral_subtype_comap measurableSet_Ioi (fun x : ℝ => x^2 • F x)

end Work.CoreResiduals.BiotSavart.KfBall

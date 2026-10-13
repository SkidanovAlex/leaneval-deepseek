import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.BiotSavart.TaylorDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- For a pointwise nonnegative function on `ℝ³`, the Bochner set integral over a measurable set
`s` agrees with the `toReal` of the set Lebesgue integral of `ENNReal.ofReal f`.

Both sides are the Bochner/`lintegral` over the restricted measure `volume.restrict s`, so this is
Mathlib's `integral_eq_lintegral_of_nonneg_ae` applied to `μ = volume.restrict s`; measurability of
`s` is not needed for the identity (but is part of the requested interface). -/
theorem setIntegral_eq_lintegral_of_nonneg {f : Work.LWP.R3 → ℝ} {s : Set Work.LWP.R3}
    (hs : MeasurableSet s) (hmeas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (hnn : 0 ≤ f) :
    ∫ y in s, f y = (∫⁻ y in s, ENNReal.ofReal (f y)).toReal := by
  exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
    hmeas.restrict

end Work.CoreResiduals.BiotSavart

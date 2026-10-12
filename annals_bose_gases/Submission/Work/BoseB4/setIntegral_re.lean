import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB4

/-- The real part of a Bochner integral of a complex-valued function over a measurable set
equals the integral of the real part. -/
theorem setIntegral_re {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {s : Set α}
    (hs : MeasurableSet s) (F : α → ℂ) (hF : MeasureTheory.IntegrableOn F s μ) :
    ∫ x in s, (F x).re ∂μ = (∫ x in s, F x ∂μ).re := by
  -- `IntegrableOn F s μ` is `Integrable F (μ.restrict s)` and the set integral is the
  -- integral against the restricted measure, so this is Mathlib's `integral_re`.
  exact integral_re hF

end Work.BoseB4

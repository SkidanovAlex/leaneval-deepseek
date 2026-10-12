import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxBridge.Resolve

/-- The kernel `K_F(z) = (2π)⁻³∫_p F(‖p‖)cos⟪p,z⟫dp` is even in `z`: replacing `z` by `-z`
negates the inner product `⟪p,z⟫`, and `cos` is even. -/
theorem kinKernel_even (F : ℝ → ℝ) (z : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinKernel F (-z) = Submission.BoseGases.kinKernel F z := by
  simp only [Submission.BoseGases.kinKernel, inner_neg_right, Real.cos_neg]

end Work.SmallBoxBridge.Resolve

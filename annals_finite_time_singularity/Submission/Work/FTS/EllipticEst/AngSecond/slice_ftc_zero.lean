import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.AngSecond.SliceIBPDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngSecond

theorem slice_ftc_zero (g g' : ℝ → ℝ)
    (hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt g (g' θ) θ)
    (hint : IntervalIntegrable g' MeasureTheory.volume 0 (Real.pi / 2))
    (h0 : Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (h1 : Filter.Tendsto g (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    (∫ θ in Work.Spaces.Iθ, g' θ) = 0 := by
  rw [setIntegral_Iθ_eq_interval g']
  have hπ : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (f := g) (f' := g')
    (a := 0) (b := Real.pi / 2) hπ hderiv hint h0 h1
  rw [h, sub_self]

end Work.FTS.EllipticEst.AngSecond

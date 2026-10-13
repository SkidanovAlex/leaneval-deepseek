import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

theorem slice_abs_diff_le_uIoc {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |F x θ - F y θ| ≤ ∫ t in Set.uIoc y x, |Work.Spaces.pz F t θ| := by
  -- `Set.uIcc y x` lies in the open half-line `(0,∞)`.
  have hsub : Set.uIcc y x ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht
    rw [Set.uIcc] at ht
    exact lt_of_lt_of_le (lt_min hy hx) ht.1
  -- The `z`-slice of `∂_z F` is continuous there, hence interval integrable.
  have hint : IntervalIntegrable (fun t : ℝ => Work.Spaces.pz F t θ) MeasureTheory.volume y x :=
    ((hsm.pz.curry_z hθ).continuousOn.mono hsub).intervalIntegrable
  -- The slice `z ↦ F z θ` has derivative `∂_z F` throughout `uIcc y x`.
  have hderiv : ∀ t ∈ Set.uIcc y x,
      HasDerivAt (fun z : ℝ => F z θ) (Work.Spaces.pz F t θ) t :=
    fun t ht => hsm.hasDerivAt_slice hθ (hsub ht)
  -- Fundamental theorem of calculus on the interval `[y,x]`.
  have hftc : ∫ t in y..x, Work.Spaces.pz F t θ = F x θ - F y θ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [← hftc]
  -- Triangle inequality for the integral, over the unordered interval.
  have h := intervalIntegral.norm_integral_le_integral_norm_uIoc
    (a := y) (b := x) (f := fun t : ℝ => Work.Spaces.pz F t θ) (μ := MeasureTheory.volume)
  simpa only [Real.norm_eq_abs] using h

end Work.FTS.PhiStar.Honesty

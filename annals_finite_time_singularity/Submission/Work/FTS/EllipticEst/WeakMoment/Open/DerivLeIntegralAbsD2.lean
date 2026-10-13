import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.TT.SliceCoercDefs
import Submission.Work.FTS.EllipticEst.SgamBound.abs_deriv_sub_le_integral_abs_D2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.WeakMoment.Open

open scoped Real Topology Interval
open MeasureTheory Set Filter

/-- **Rolle's theorem in the form needed here**: a function which is continuous on `Iθ = [0, π/2]`
and vanishes at both endpoints has a zero of its derivative in the open interval. -/
private theorem exists_deriv_eq_zero_on_Iθ {u : ℝ → ℝ}
    (hcont : ContinuousOn u Work.Spaces.Iθ) (h0 : u 0 = 0) (hpi : u (Real.pi / 2) = 0) :
    ∃ θ₀ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), deriv u θ₀ = 0 := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have hcont' : ContinuousOn u (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    simpa only [Work.Spaces.Iθ] using hcont
  have hfI : u 0 = u (Real.pi / 2) := by rw [h0, hpi]
  exact exists_deriv_eq_zero hpi2 hcont' hfI

theorem DerivLeIntegralAbsD2 {u : ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hcont : ContinuousOn u Work.Spaces.Iθ) (h0 : u 0 = 0) (hpi : u (Real.pi / 2) = 0)
    (habs : MeasureTheory.IntegrableOn
      (fun θ : ℝ => |Work.FTS.EllipticEst.TT.D2 u θ|) Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv u θ| ≤ ∫ x in Work.Spaces.Iθ, |Work.FTS.EllipticEst.TT.D2 u x| := by
  -- Rolle: the derivative has an interior zero because `u` vanishes at both endpoints.
  obtain ⟨θ₀, hθ₀, hzero⟩ := exists_deriv_eq_zero_on_Iθ hcont h0 hpi
  intro θ hθ
  -- The fundamental theorem of calculus on the segment `[θ₀, θ]` and the triangle
  -- inequality for the integral.
  have h := Work.FTS.EllipticEst.SgamBound.abs_deriv_sub_le_integral_abs_D2 hsm habs hθ hθ₀
  simpa only [hzero, sub_zero] using h

end Work.FTS.EllipticEst.WeakMoment.Open

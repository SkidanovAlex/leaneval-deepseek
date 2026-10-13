import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.Honest.I4SliceDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

theorem I4SubInterval (f : ℝ → ℝ) (hA : MeasureTheory.IntegrableOn f Work.Spaces.Iθ)
    (hnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ f θ)
    {δ θ₁ : ℝ} (hδ : 0 ≤ δ) (hδθ : δ ≤ θ₁) (hθ₁ : θ₁ ≤ Real.pi / 2) :
    (∫ θ in δ..θ₁, f θ) ≤ (∫ θ in Work.Spaces.Iθ, f θ) := by
  -- `Iθ = [0, π/2]`, and `[δ, θ₁] ⊆ Iθ`; so the interval integral is a sub-integral of a
  -- nonnegative function over a larger set.
  have hsub : Set.Ioc δ θ₁ ⊆ Work.Spaces.Iθ := by
    intro θ hθ
    exact ⟨by linarith [hδ, hθ.1.le], by linarith [hθ.2, hθ₁]⟩
  rw [intervalIntegral.integral_of_le hδθ]
  refine MeasureTheory.setIntegral_mono_set hA ?_ ?_
  · filter_upwards
      [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc] with θ hθ
    exact hnn θ hθ
  · exact Filter.Eventually.of_forall hsub

end Work.FTS.EllipticEst.Honest

import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.Defs
import Submission.Work.StabilityFar.Decay.biotSavart_sub
import Submission.Work.StabilityFar.Decay.KernelDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory

/-- The Biot–Savart integrand `bsK` (see `Work.LWP.BiotSavart.bsK`) is additive in the vorticity:
the cross product is additive in its first slot (`Work.StabilityFar.Decay.crossL_add`, via
`Work.StabilityFar.Decay.bsK_eq_crossL`), and the scalar factor `‖x - y‖⁻³` is common. -/
lemma bsK_add (f g : Work.LWP.R3 → Work.LWP.R3) (x y : Work.LWP.R3) :
    Work.LWP.BiotSavart.bsK (fun a => f a + g a) x y
      = Work.LWP.BiotSavart.bsK f x y + Work.LWP.BiotSavart.bsK g x y := by
  rw [Work.StabilityFar.Decay.bsK_eq_crossL, Work.StabilityFar.Decay.bsK_eq_crossL,
    Work.StabilityFar.Decay.bsK_eq_crossL, Work.StabilityFar.Decay.crossL_add, add_apply]

/-- The Biot–Savart operator is additive: for an additively combined vorticity, `biotSavart` splits.  Both inputs are bounded, supported in a common ball and ae-strongly-measurable, so each integrand is dominated by `M·‖x-y‖⁻²` on that ball (integrable in `ℝ³`). -/
theorem biotSavart_add {ω₁ ω₂ : Work.LWP.R3 → Work.LWP.R3} {R M₁ M₂ : ℝ}
    (hω₁ : ∀ a, ‖ω₁ a‖ ≤ M₁) (hω₂ : ∀ a, ‖ω₂ a‖ ≤ M₂)
    (hs₁ : ∀ a, ω₁ a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hs₂ : ∀ a, ω₂ a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hm₁ : MeasureTheory.AEStronglyMeasurable ω₁ MeasureTheory.volume)
    (hm₂ : MeasureTheory.AEStronglyMeasurable ω₂ MeasureTheory.volume) (x : Work.LWP.R3) :
    Work.LWP.biotSavart (fun a => ω₁ a + ω₂ a) x
      = Work.LWP.biotSavart ω₁ x + Work.LWP.biotSavart ω₂ x := by
  -- The bounds `M₁, M₂` are non-negative, since they dominate a norm.
  have hM₁ : 0 ≤ M₁ := le_trans (norm_nonneg (ω₁ 0)) (hω₁ 0)
  have hM₂ : 0 ≤ M₂ := le_trans (norm_nonneg (ω₂ 0)) (hω₂ 0)
  -- Each integrand is Bochner-integrable: bounded and supported in `B(0,R)`, the (singular)
  -- kernel is dominated by `M·‖x-y‖⁻²` on that ball, which is integrable in `ℝ³`.
  have hi₁ : Integrable (Work.LWP.BiotSavart.bsK ω₁ x) volume :=
    Work.StabilityFar.Decay.integrable_bsK_supported hM₁ hω₁ hs₁ hm₁ x
  have hi₂ : Integrable (Work.LWP.BiotSavart.bsK ω₂ x) volume :=
    Work.StabilityFar.Decay.integrable_bsK_supported hM₂ hω₂ hs₂ hm₂ x
  -- Unfold `biotSavart` into `(4π)⁻¹ • ∫ bsK`, split the integrand pointwise, use additivity of
  -- the Bochner integral, and distribute the scalar.
  rw [Work.LWP.BiotSavart.biotSavart_apply, Work.LWP.BiotSavart.biotSavart_apply,
    Work.LWP.BiotSavart.biotSavart_apply]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun y => bsK_add ω₁ ω₂ x y)]
  rw [integral_add hi₁ hi₂, smul_add]

end Work.CoreResiduals.BiotSavart

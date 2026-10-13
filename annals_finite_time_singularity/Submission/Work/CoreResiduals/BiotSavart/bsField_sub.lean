import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.BiotSavart.DerivDefs
import Submission.Work.StabilityFar.Decay.biotSavart_sub

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric

/-- **Additivity of the `bsField` integral under a shift of the evaluation point.**

`bsField ω ρ` is the Bochner integral over the fixed ball `B(0,ρ)` of the integrand
`a ↦ crossL (ω a) (kf (· - a))`.  The Bochner integral is additive in the integrand, so the
difference of the two integrals at `x + h` and at `x` is the integral of the difference — the
only content being that both shifted integrands are absolutely integrable, which is
`Work.StabilityFar.Decay.integrable_bsK_supported` transported along
`Work.StabilityFar.Decay.bsK_eq_crossL`. -/
theorem bsField_sub {ω : Work.LWP.R3 → Work.LWP.R3} {R M : ℝ} (hM : 0 ≤ M)
    (hbdd : ∀ a, ‖ω a‖ ≤ M) (hs : ∀ a, ω a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hm : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume) (ρ : ℝ) (x h : Work.LWP.R3) :
    Work.CoreResiduals.BiotSavart.bsField ω ρ (x + h) - Work.CoreResiduals.BiotSavart.bsField ω ρ x
      = ∫ a in Metric.ball (0 : Work.LWP.R3) ρ,
          Work.StabilityFar.Decay.crossL (ω a)
            (Work.StabilityFar.Decay.kf (x + h - a) - Work.StabilityFar.Decay.kf (x - a)) := by
  -- The integrand `a ↦ crossL (ω a) (kf (y - a))` is `bsK ω y`, hence absolutely integrable on
  -- all of `ℝ³` for `y = x` and `y = x + h`.
  have hI1 : MeasureTheory.Integrable
      (fun a => Work.StabilityFar.Decay.crossL (ω a) (Work.StabilityFar.Decay.kf (x + h - a)))
      MeasureTheory.volume :=
    (Work.StabilityFar.Decay.integrable_bsK_supported hM hbdd hs hm (x + h)).congr
      (Filter.Eventually.of_forall fun a =>
        Work.StabilityFar.Decay.bsK_eq_crossL ω (x + h) a)
  have hI2 : MeasureTheory.Integrable
      (fun a => Work.StabilityFar.Decay.crossL (ω a) (Work.StabilityFar.Decay.kf (x - a)))
      MeasureTheory.volume :=
    (Work.StabilityFar.Decay.integrable_bsK_supported hM hbdd hs hm x).congr
      (Filter.Eventually.of_forall fun a =>
        Work.StabilityFar.Decay.bsK_eq_crossL ω x a)
  -- Restricting to the ball `B(0,ρ)` preserves integrability.
  have h1 : MeasureTheory.Integrable
      (fun a => Work.StabilityFar.Decay.crossL (ω a) (Work.StabilityFar.Decay.kf (x + h - a)))
      (MeasureTheory.volume.restrict (Metric.ball (0 : Work.LWP.R3) ρ)) := hI1.integrableOn
  have h2 : MeasureTheory.Integrable
      (fun a => Work.StabilityFar.Decay.crossL (ω a) (Work.StabilityFar.Decay.kf (x - a)))
      (MeasureTheory.volume.restrict (Metric.ball (0 : Work.LWP.R3) ρ)) := hI2.integrableOn
  -- Unfold the two `bsField`s into the corresponding restricted Bochner integrals.
  rw [Work.CoreResiduals.BiotSavart.bsField.eq_def, Work.CoreResiduals.BiotSavart.bsField.eq_def]
  -- Move the linear map `crossL (ω a)` inside the difference, pointwise in `a`.
  rw [show (∫ a in Metric.ball (0 : Work.LWP.R3) ρ,
        Work.StabilityFar.Decay.crossL (ω a)
          (Work.StabilityFar.Decay.kf (x + h - a) - Work.StabilityFar.Decay.kf (x - a)))
      = ∫ a in Metric.ball (0 : Work.LWP.R3) ρ,
          (Work.StabilityFar.Decay.crossL (ω a) (Work.StabilityFar.Decay.kf (x + h - a))
            - Work.StabilityFar.Decay.crossL (ω a) (Work.StabilityFar.Decay.kf (x - a))) by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with a
        exact map_sub (Work.StabilityFar.Decay.crossL (ω a)) _ _]
  -- Split the integral of the difference using integrability of both pieces.
  rw [MeasureTheory.integral_sub h1 h2]

end Work.CoreResiduals.BiotSavart

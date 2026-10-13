/-
# `Work.CoreResiduals.BiotSavart.integrable_indicator_kDerivCLM_annulus`

Bochner integrability of the derivative of the Newtonian kernel on a centred annulus.

The kernel `kDerivCLM b = ‖b‖⁻³ • Id − 3‖b‖⁻⁵ • (innerSL ℝ b).smulRight b` blows up like
`‖b‖⁻³` at the origin, but on an annulus `r < ‖b‖ < ρ` with `r > 0` the norm is bounded by the
*constant* `4 r⁻³`; the annulus has finite volume (it sits inside `B(0,ρ)`), so the integrand is
dominated by a bounded function on a finite-measure set.

The two inputs are `Work.StabilityFar.Decay.norm_kDerivCLM_le` (the pointwise bound
`‖kDerivCLM b‖ ≤ 4 / m³` whenever `m ≤ ‖b‖`) and `Work.StabilityFar.Decay.continuousAt_kDerivCLM`
(continuity away from the origin, giving the measurability on the annulus).
-/
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.LWP.Defs
import Submission.Work.StabilityFar.Decay.decay_aux
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric

namespace Work.CoreResiduals.BiotSavart

/-- The derivative of the Newtonian kernel is Bochner-integrable on the annulus
`r < ‖b‖ < ρ`, provided `r > 0`: there the kernel is bounded by the constant `4 r⁻³` and the
annulus has finite volume. -/
theorem integrable_indicator_kDerivCLM_annulus {r ρ : ℝ} (hr : 0 < r) :
    MeasureTheory.Integrable
      ((Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball (0 : Work.LWP.R3) r).indicator
        (fun b => Work.StabilityFar.Decay.kDerivCLM b)) MeasureTheory.volume := by
  classical
  have hmeasSet : MeasurableSet
      (Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball (0 : Work.LWP.R3) r) :=
    Metric.isOpen_ball.measurableSet.diff Metric.isOpen_ball.measurableSet
  have hfin : volume (Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball (0 : Work.LWP.R3) r) < ⊤ := by
    calc volume (Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball (0 : Work.LWP.R3) r)
        ≤ volume (Metric.ball (0 : Work.LWP.R3) ρ) := measure_mono Set.sdiff_subset
      _ < ⊤ := measure_ball_lt_top
  -- On the annulus, `b` stays at distance at least `r` from the origin.
  have hb2 : ∀ b ∈ (Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball (0 : Work.LWP.R3) r),
      r ≤ ‖b‖ := by
    intro b hb
    have h := hb.2
    simp only [Metric.mem_ball, dist_zero_right, not_lt] at h
    exact h
  have key : MeasureTheory.IntegrableOn
      (fun b : Work.LWP.R3 => Work.StabilityFar.Decay.kDerivCLM b)
      (Metric.ball (0 : Work.LWP.R3) ρ \ Metric.ball (0 : Work.LWP.R3) r) MeasureTheory.volume := by
    refine MeasureTheory.IntegrableOn.of_bound hfin ?_ (4 / r ^ 3) ?_
    · -- measurability: `kDerivCLM` is continuous at every point of the annulus
      apply ContinuousOn.aestronglyMeasurable _ hmeasSet
      intro b hb
      have hb0 : b ≠ 0 := by
        have : 0 < ‖b‖ := lt_of_lt_of_le hr (hb2 b hb)
        exact norm_pos_iff.mp this
      exact (Work.StabilityFar.Decay.continuousAt_kDerivCLM hb0).continuousWithinAt
    · -- the uniform bound `‖kDerivCLM b‖ ≤ 4 / r³`
      filter_upwards [ae_restrict_mem hmeasSet] with b hb
      exact Work.StabilityFar.Decay.norm_kDerivCLM_le b r hr (hb2 b hb)
  exact (MeasureTheory.integrable_indicator_iff
    (f := fun b : Work.LWP.R3 => Work.StabilityFar.Decay.kDerivCLM b) hmeasSet).mpr key

end Work.CoreResiduals.BiotSavart

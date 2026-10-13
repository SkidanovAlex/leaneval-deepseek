import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.LWP.BiotSavart.farField_decay_fderiv
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.norm_crossL_le
import Submission.Work.CoreResiduals.BiotSavart.TaylorDefs
import Submission.Work.CoreResiduals.BiotSavart.norm_bsField_diff_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric

/-- **Integrability of the Biot–Savart integrand on a ball.**

For a time slice `ω · t` of the vorticity which is bounded by `M ≥ 0` and a.e. strongly
measurable, the integrand

  `a ↦ crossL (ω a t) (kf (x - a))`

is Bochner-integrable on the ball `B(0,ρ)`.

The singularity of the kernel `kf` sits at `a = x` and is of size `‖x - a‖⁻²`; in dimension `3`
the exponent `2` is below the integrability threshold `3`, so the singular weight is locally
integrable.  Concretely, the norm of the integrand is dominated by the *integrable* weight
`M ‖kf (x - ·)‖` (`Work.CoreResiduals.BiotSavart.integrableOn_kf_sub`), which gives the claim
through the domination criterion `Work.CoreResiduals.BiotSavart.integrableOn_of_norm_le_ball`;
measurability is `Work.CoreResiduals.BiotSavart.aestronglyMeasurable_crossL_kf`. -/
theorem integrableOn_crossL_kf_ball {ω : Work.LWP.R3 → ℝ → Work.LWP.R3}
    {M ρ : ℝ} {x : Work.LWP.R3} {t : ℝ}
    (hM : 0 ≤ M) (hbdd : ∀ y : Work.LWP.R3, ‖ω y t‖ ≤ M)
    (hmeas : MeasureTheory.AEStronglyMeasurable (ω · t) MeasureTheory.volume) :
    MeasureTheory.IntegrableOn
      (fun a : Work.LWP.R3 =>
        Work.StabilityFar.Decay.crossL (ω a t) (Work.StabilityFar.Decay.kf (x - a)))
      (Metric.ball (0 : Work.LWP.R3) ρ) MeasureTheory.volume := by
  -- Measurability of the integrand.
  have hmeas' : MeasureTheory.AEStronglyMeasurable
      (fun a : Work.LWP.R3 =>
        Work.StabilityFar.Decay.crossL (ω a t) (Work.StabilityFar.Decay.kf (x - a)))
      MeasureTheory.volume :=
    aestronglyMeasurable_crossL_kf hmeas x
  -- The dominating weight `M ‖kf (x - ·)‖` is integrable on the ball.
  have hdom : MeasureTheory.IntegrableOn
      (fun a : Work.LWP.R3 => M * ‖Work.StabilityFar.Decay.kf (x - a)‖)
      (Metric.ball (0 : Work.LWP.R3) ρ) MeasureTheory.volume :=
    ((integrableOn_kf_sub x ρ).norm).const_mul M
  -- Pointwise domination by the weight.
  refine integrableOn_of_norm_le_ball hdom hmeas' (fun a _ => ?_)
  calc ‖Work.StabilityFar.Decay.crossL (ω a t) (Work.StabilityFar.Decay.kf (x - a))‖
      ≤ ‖Work.StabilityFar.Decay.crossL (ω a t)‖ * ‖Work.StabilityFar.Decay.kf (x - a)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖ω a t‖ * ‖Work.StabilityFar.Decay.kf (x - a)‖ :=
        mul_le_mul_of_nonneg_right (Work.StabilityFar.Decay.norm_crossL_le _) (norm_nonneg _)
    _ ≤ M * ‖Work.StabilityFar.Decay.kf (x - a)‖ :=
        mul_le_mul (hbdd a) le_rfl (norm_nonneg _) hM

end Work.CoreResiduals.BiotSavart

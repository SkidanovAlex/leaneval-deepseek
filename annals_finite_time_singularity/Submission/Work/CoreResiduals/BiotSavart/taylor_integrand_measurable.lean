import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.BiotSavart.TaylorDefs
import Submission.Work.StabilityFar.Decay.decay_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.CoreResiduals.BiotSavart

open Work.StabilityFar.Decay

/-- A map satisfying the norm form of a Hölder estimate with exponent `c > 0` (and any constant
`C`, nonnegative or not) is continuous: the right-hand side tends to `0` at every point. -/
theorem continuous_of_norm_holder {ω : Work.LWP.R3 → Work.LWP.R3} {c C : ℝ}
    (hc : 0 < c) (hhold : ∀ a b : Work.LWP.R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c) :
    Continuous ω := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun a => norm_nonneg _) (fun a => hhold a x) ?_
  have h1 : Filter.Tendsto (fun a : Work.LWP.R3 => ‖a - x‖) (nhds x) (nhds 0) := by
    have h := (continuous_id.sub continuous_const :
      Continuous fun a : Work.LWP.R3 => a - x).tendsto x
    simpa using h.norm
  have h2 : Filter.Tendsto (fun a : Work.LWP.R3 => ‖a - x‖ ^ c) (nhds x) (nhds 0) := by
    have h := h1.rpow tendsto_const_nhds (Or.inr hc)
    simpa [Real.zero_rpow hc.ne'] using h
  simpa using h2.const_mul C

theorem taylor_integrand_measurable {ω : Work.LWP.R3 → Work.LWP.R3} {c C : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C)
    (hhold : ∀ a b : Work.LWP.R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c) (x h : Work.LWP.R3) :
    MeasureTheory.AEStronglyMeasurable (fun a : Work.LWP.R3 =>
      ‖Work.StabilityFar.Decay.crossL (ω a - ω x)
        (Work.CoreResiduals.BiotSavart.resid h (x - a))‖) MeasureTheory.volume := by
  have hωc : Continuous ω := continuous_of_norm_holder hc hhold
  have hωm : MeasureTheory.AEStronglyMeasurable (fun a : Work.LWP.R3 => ω a - ω x)
      MeasureTheory.volume := (hωc.sub continuous_const).aestronglyMeasurable
  have hres : MeasureTheory.AEStronglyMeasurable
      (fun a : Work.LWP.R3 => resid h (x - a)) MeasureTheory.volume := by
    apply Measurable.aestronglyMeasurable
    unfold resid Work.StabilityFar.Decay.kf Work.StabilityFar.Decay.kDerivCLM
    measurability
  have hpair : MeasureTheory.AEStronglyMeasurable
      (fun a : Work.LWP.R3 => (ω a - ω x, resid h (x - a))) MeasureTheory.volume :=
    hωm.prodMk hres
  have hcont : Continuous (fun p : Work.LWP.R3 × Work.LWP.R3 => crossL p.1 p.2) :=
    (continuous_crossL.comp continuous_fst).clm_apply continuous_snd
  exact (hcont.comp_aestronglyMeasurable hpair).norm

end Work.CoreResiduals.BiotSavart

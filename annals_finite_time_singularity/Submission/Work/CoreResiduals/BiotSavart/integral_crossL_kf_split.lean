import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.LWP.Defs
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.LWP.BiotSavart.farField_decay_fderiv
import Submission.Work.CoreResiduals.BiotSavart.integral_ball_sub_norm_rpow
import Submission.Work.CoreResiduals.BiotSavart.integrableOn_crossL_kf_ball
import Submission.Work.StabilityFar.Decay.norm_crossL_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Set

-- The interface of this lemma carries the hypotheses `hM`, `hΔ`, `hx` (the bound on the vorticity
-- slice, the radius of the cut-off ball and the location of the centre) because callers use them to
-- control the two pieces; the *splitting identity* itself needs only that the integrand be
-- integrable on the bounded ball `B(0,ρ)` — which is `integrableOn_crossL_kf_ball`, proved by a
-- single domination — while `hΔ` and `hx` enter the two-piece estimates (the outer piece being
-- bounded by `M * (Δ/2)⁻²`), not the identity.  Hence they are deliberately not referenced here.
set_option linter.unusedVariables false

/-- **Splitting the Biot–Savart integral at a fixed centre.**

For a vorticity slice bounded by `M ≥ 0` and `x ∈ B(x₀,Δ/2)` with `Δ > 0`, the integral of the
Biot–Savart integrand over the fixed ball `B(0,ρ)` is the sum of its parts over
`B(0,ρ) ∩ B(x₀,Δ)` and over `B(0,ρ) \ B(x₀,Δ)`.

The two pieces are integrable (which is what makes the split legitimate): on the inner piece the
integrand is dominated by `M ‖x - ·‖⁻²` (an integrable singular weight on a bounded set, cf.
`Work.CoreResiduals.BiotSavart.integral_ball_sub_norm_rpow`), and on the outer piece by the
constant `M * (Δ/2)⁻²` on the finite-measure set `B(0,ρ)` (using `‖x - a‖ ≥ Δ/2`, which is where
`hx` is used). Measurability of the integrand comes from
`Work.LWP.BiotSavart.aestronglyMeasurable_bsK` together with
`Work.StabilityFar.Decay.bsK_eq_crossL`. -/
theorem integral_crossL_kf_split {ω : Work.LWP.R3 → ℝ → Work.LWP.R3}
    {M ρ Δ : ℝ} {x₀ x : Work.LWP.R3} {t : ℝ}
    (hM : 0 ≤ M) (hbdd : ∀ y : Work.LWP.R3, ‖ω y t‖ ≤ M)
    (hmeas : MeasureTheory.AEStronglyMeasurable (ω · t) MeasureTheory.volume)
    (hΔ : 0 < Δ) (hx : ‖x - x₀‖ ≤ Δ / 2) :
    (∫ a in Metric.ball (0 : Work.LWP.R3) ρ,
        Work.StabilityFar.Decay.crossL (ω a t) (Work.StabilityFar.Decay.kf (x - a)))
      = (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ),
            Work.StabilityFar.Decay.crossL (ω a t) (Work.StabilityFar.Decay.kf (x - a)))
        + (∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) \ (Metric.ball x₀ Δ),
            Work.StabilityFar.Decay.crossL (ω a t) (Work.StabilityFar.Decay.kf (x - a))) := by
  -- The integrand is Bochner-integrable on the bounded ball `B(0,ρ)`: the weight
  -- `‖kf (x - a)‖ = ‖x - a‖⁻²` has a singularity of order `2 < 3` in dimension three, so it may be
  -- integrated across `a = x`.
  have hf_int : MeasureTheory.IntegrableOn
      (fun a : Work.LWP.R3 =>
        Work.StabilityFar.Decay.crossL (ω a t) (Work.StabilityFar.Decay.kf (x - a)))
      (Metric.ball (0 : Work.LWP.R3) ρ) MeasureTheory.volume :=
    integrableOn_crossL_kf_ball hM hbdd hmeas
  -- `B(0,ρ) = (B(0,ρ) ∩ B(x₀,Δ)) ⊔ (B(0,ρ) \ B(x₀,Δ))` is a partition into measurable sets, so
  -- the integral over `B(0,ρ)` is the sum of the integrals over the two parts.
  exact (MeasureTheory.integral_inter_add_sdiff₀
    (s := Metric.ball (0 : Work.LWP.R3) ρ) (t := Metric.ball x₀ Δ)
    measurableSet_ball.nullMeasurableSet hf_int).symm

end Work.CoreResiduals.BiotSavart

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.LWP.Defs
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.LWP.BiotSavart.farField_decay_fderiv
import Submission.Work.CoreResiduals.BiotSavart.integral_ball_sub_norm_rpow
import Submission.Work.StabilityFar.Decay.norm_crossL_le
import Submission.Work.CoreResiduals.BiotSavart.TaylorDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Set

/-- Integrability of the inverse-square weight `‖· - x‖⁻²` on a ball centred at `x`.

The exponent `-2 > -3 = -finrank ℝ ℝ³` is sub-critical, so the singularity is absolutely
integrable: the value of the integral is `4π R` by `integral_ball_sub_norm_rpow`, hence the
integral is not the `0` of a non-integrable function. -/
private lemma integrableOn_norm_sub_rpow_neg_two (x : Work.LWP.R3) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun a : Work.LWP.R3 => (‖a - x‖ : ℝ) ^ (-2 : ℝ)) (Metric.ball x R) volume := by
  have hval := integral_ball_sub_norm_rpow x R (-2) (by norm_num) hR
  have hpos : 0 < 4 * Real.pi * R ^ ((-2 : ℝ) + 3) / ((-2 : ℝ) + 3) := by
    rw [show (-2 : ℝ) + 3 = 1 by norm_num, Real.rpow_one, div_one]
    positivity
  by_contra hcon
  have h0 := integral_undef hcon
  rw [hval] at h0
  exact absurd h0 (ne_of_gt hpos)

/-- **The inner piece of the Biot–Savart integral is uniformly small.**

For a vorticity slice bounded by `M ≥ 0`, the integral of the Biot–Savart integrand over the
*disc* `B(0,ρ) ∩ B(x₀,Δ)` centred at the fixed point `x₀` is bounded, uniformly in
`x ∈ B(x₀,Δ/2)`, by `M * (4π * (3Δ/2))`: the integrand is dominated by the singular weight
`M ‖x - ·‖⁻²` (`norm_bsK_le`), the set is contained in `B(x,3Δ/2)`, and the radial integral
`∫_{B(x,r)}‖x - a‖⁻² da = 4π r` comes from
`Work.CoreResiduals.BiotSavart.integral_ball_sub_norm_rpow` at `s = -2`.

No measurability hypothesis is needed: `MeasureTheory.norm_integral_le_of_norm_le` only requires
the dominating function to be integrable. -/
theorem norm_setIntegral_crossL_kf_inter_le {ω : Work.LWP.R3 → ℝ → Work.LWP.R3}
    {M ρ Δ : ℝ} {x₀ x : Work.LWP.R3} {t : ℝ}
    (hM : 0 ≤ M) (hbdd : ∀ y : Work.LWP.R3, ‖ω y t‖ ≤ M)
    (hΔ : 0 < Δ) (hx : ‖x - x₀‖ ≤ Δ / 2) :
    ‖∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ),
        Work.StabilityFar.Decay.crossL (ω a t) (Work.StabilityFar.Decay.kf (x - a))‖
      ≤ M * (4 * Real.pi * (3 * Δ / 2)) := by
  have h3Δ : 0 < 3 * Δ / 2 := by linarith
  have hxx₀ : dist x₀ x ≤ Δ / 2 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hx
  -- The relevant disc is contained in the ball `B(x, 3Δ/2)` around the singularity.
  have hsub : (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ)
      ⊆ Metric.ball x (3 * Δ / 2) := by
    intro a ha
    rw [Metric.mem_ball]
    have ha2 : dist a x₀ < Δ := by
      simpa only [Metric.mem_ball] using ha.2
    calc dist a x ≤ dist a x₀ + dist x₀ x := dist_triangle a x₀ x
      _ < Δ + Δ / 2 := add_lt_add_of_lt_of_le ha2 hxx₀
      _ = 3 * Δ / 2 := by ring
  -- The dominating weight is integrable on `B(x, 3Δ/2)`, hence on the disc.
  have hIntX : IntegrableOn (fun a : Work.LWP.R3 => M * (‖a - x‖ : ℝ) ^ (-2 : ℝ))
      (Metric.ball x (3 * Δ / 2)) volume :=
    (integrableOn_norm_sub_rpow_neg_two x h3Δ).const_mul M
  have hInts : IntegrableOn (fun a : Work.LWP.R3 => M * (‖a - x‖ : ℝ) ^ (-2 : ℝ))
      ((Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ)) volume :=
    hIntX.mono_set hsub
  calc ‖∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ),
        Work.StabilityFar.Decay.crossL (ω a t) (Work.StabilityFar.Decay.kf (x - a))‖
      ≤ ∫ a in (Metric.ball (0 : Work.LWP.R3) ρ) ∩ (Metric.ball x₀ Δ),
          M * (‖a - x‖ : ℝ) ^ (-2 : ℝ) :=
        MeasureTheory.norm_integral_le_of_norm_le hInts
          (Filter.Eventually.of_forall fun a => by
            calc ‖Work.StabilityFar.Decay.crossL (ω a t) (Work.StabilityFar.Decay.kf (x - a))‖
                ≤ ‖Work.StabilityFar.Decay.crossL (ω a t)‖
                    * ‖Work.StabilityFar.Decay.kf (x - a)‖ :=
                  ContinuousLinearMap.le_opNorm _ _
              _ ≤ ‖ω a t‖ * ‖Work.StabilityFar.Decay.kf (x - a)‖ :=
                  mul_le_mul_of_nonneg_right (Work.StabilityFar.Decay.norm_crossL_le _)
                    (norm_nonneg _)
              _ ≤ M * ‖Work.StabilityFar.Decay.kf (x - a)‖ :=
                  mul_le_mul_of_nonneg_right (hbdd a) (norm_nonneg _)
              _ = M * (‖a - x‖ : ℝ) ^ (-2 : ℝ) := by
                  rw [Work.CoreResiduals.BiotSavart.norm_kf_eq, norm_sub_rev])
    _ ≤ ∫ a in Metric.ball x (3 * Δ / 2), M * (‖a - x‖ : ℝ) ^ (-2 : ℝ) :=
        setIntegral_mono_set hIntX
          (Filter.Eventually.of_forall fun a =>
            mul_nonneg hM (Real.rpow_nonneg (norm_nonneg _) _))
          (Filter.Eventually.of_forall fun a ha => hsub ha)
    _ = M * (4 * Real.pi * (3 * Δ / 2)) := by
        rw [integral_const_mul]
        congr 1
        rw [integral_ball_sub_norm_rpow x (3 * Δ / 2) (-2) (by norm_num) h3Δ,
          show (-2 : ℝ) + 3 = 1 by norm_num, Real.rpow_one, div_one]

end Work.CoreResiduals.BiotSavart

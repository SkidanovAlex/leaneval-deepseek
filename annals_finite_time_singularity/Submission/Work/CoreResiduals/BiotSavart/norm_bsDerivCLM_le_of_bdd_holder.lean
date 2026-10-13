/-
# `Work.CoreResiduals.BiotSavart.norm_bsDerivCLM_le_of_bdd_holder` — a uniform bound on the
candidate Biot–Savart derivative

For a vorticity `g` that is bounded by `A ≥ 0` and `α`-Hölder with constant `2H ≥ 0`
(`0 < α < 1`), the candidate derivative
`bsDerivCLM g ρ x = ∫_{B(0,ρ)} (crossL (g a - g x)).comp (kDerivCLM (x - a)) + (4π/3) • crossL (g x)`
obeys the interpolation bound

  `‖bsDerivCLM g ρ x‖ ≤ 4 (2A)^α (2H)^{1-α} · 4π (ρ + ‖x‖)^{α(1-α)} / (α(1-α)) + (4π/3) A`.

The two ingredients are the pointwise interpolation bound for the integrand
`‖bsIntegrand g x a‖ ≤ 4 (2A)^α (2H)^{1-α} ‖x - a‖^{α(1-α)-3}`
(`Work.CoreResiduals.BiotSavart.norm_bsIntegrand_le_interp`, from
`‖g a - g x‖ ≤ min(2A, 2H‖a - x‖^α) ≤ (2A)^α (2H‖a - x‖^α)^{1-α}`), and the radial integral
over the ball `B(0,ρ) ⊆ B(x, ρ + ‖x‖)`
(`Work.CoreResiduals.BiotSavart.setIntegral_ball_zero_norm_sub_rpow_le`).
-/
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.BiotSavart.DerivDefs
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_le
import Submission.Work.StabilityFar.Decay.norm_crossL_le
import Submission.Work.CoreResiduals.BiotSavart.integral_ball_sub_norm_rpow
import Submission.Work.CoreResiduals.BiotSavart.continuous_bsDerivCLM
import Submission.Work.CoreResiduals.BiotSavart.TaylorDefs
import Submission.Work.CoreResiduals.BiotSavart.IntegrandDefs
import Submission.Work.CoreResiduals.BiotSavart.norm_bsIntegrand_le_interp
import Submission.Work.CoreResiduals.BiotSavart.setIntegral_ball_zero_norm_sub_rpow_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric
open Work.StabilityFar.Decay

theorem norm_bsDerivCLM_le_of_bdd_holder {α A H ρ : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hA : 0 ≤ A) (hH : 0 ≤ H) (hρ : 0 ≤ ρ)
    {g : Work.LWP.R3 → Work.LWP.R3}
    (hbdd : ∀ a, ‖g a‖ ≤ A)
    (hhold : ∀ a b : Work.LWP.R3, ‖g a - g b‖ ≤ 2 * H * ‖a - b‖ ^ α)
    (x : Work.LWP.R3) :
    ‖Work.CoreResiduals.BiotSavart.bsDerivCLM g ρ x‖ ≤
      4 * (2 * A) ^ α * (2 * H) ^ (1 - α) *
        (4 * Real.pi * (ρ + ‖x‖) ^ (α * (1 - α)) / (α * (1 - α)))
      + (4 * Real.pi / 3) * A := by
  have hspos : 0 < α * (1 - α) := mul_pos hα (by linarith)
  have hs : (-3 : ℝ) < α * (1 - α) - 3 := by linarith
  have hKnn : 0 ≤ 4 * (2 * A) ^ α * (2 * H) ^ (1 - α) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) α))
      (Real.rpow_nonneg (by linarith) (1 - α))
  -- pointwise interpolation bound for the integrand
  have hpt : ∀ a, ‖bsIntegrand g x a‖ ≤
      4 * (2 * A) ^ α * (2 * H) ^ (1 - α) * ‖x - a‖ ^ (α * (1 - α) - 3) :=
    fun a => norm_bsIntegrand_le_interp hα hα1 hA hH hbdd hhold x a
  -- integrability of the dominating function on `B(0,ρ)`
  have hInt : IntegrableOn (fun a : Work.LWP.R3 =>
      4 * (2 * A) ^ α * (2 * H) ^ (1 - α) * ‖x - a‖ ^ (α * (1 - α) - 3))
      (Metric.ball (0 : Work.LWP.R3) ρ) volume := by
    rcases eq_or_lt_of_le hρ with hρ0 | hρpos
    · rw [← hρ0, Metric.ball_zero]
      exact integrableOn_empty
    · have hRpos : 0 < ρ + ‖x‖ := by linarith [norm_nonneg x]
      have hsub : Metric.ball (0 : Work.LWP.R3) ρ ⊆ Metric.ball x (ρ + ‖x‖) := by
        intro a ha
        rw [Metric.mem_ball, dist_zero_right] at ha
        rw [Metric.mem_ball, dist_eq_norm]
        calc ‖a - x‖ ≤ ‖a‖ + ‖x‖ := norm_sub_le a x
          _ < ρ + ‖x‖ := by linarith
      have hbase : IntegrableOn (fun a : Work.LWP.R3 => ‖x - a‖ ^ (α * (1 - α) - 3))
          (Metric.ball (0 : Work.LWP.R3) ρ) volume := by
        have h1 :=
          (integrableOn_norm_sub_rpow_ball x (c := α * (1 - α)) hspos hRpos).mono_set hsub
        simpa only [norm_sub_rev] using h1
      exact hbase.const_mul _
  -- the integral term is bounded by the radial estimate
  have hIntBound : ‖∫ a in Metric.ball (0 : Work.LWP.R3) ρ, bsIntegrand g x a‖ ≤
      4 * (2 * A) ^ α * (2 * H) ^ (1 - α) *
        (4 * Real.pi * (ρ + ‖x‖) ^ (α * (1 - α)) / (α * (1 - α))) := by
    have h1 := MeasureTheory.norm_integral_le_of_norm_le hInt (Filter.Eventually.of_forall hpt)
    calc ‖∫ a in Metric.ball (0 : Work.LWP.R3) ρ, bsIntegrand g x a‖
        ≤ ∫ a in Metric.ball (0 : Work.LWP.R3) ρ,
            4 * (2 * A) ^ α * (2 * H) ^ (1 - α) * ‖x - a‖ ^ (α * (1 - α) - 3) := h1
      _ = 4 * (2 * A) ^ α * (2 * H) ^ (1 - α) *
            ∫ a in Metric.ball (0 : Work.LWP.R3) ρ, ‖x - a‖ ^ (α * (1 - α) - 3) := by
          rw [integral_const_mul]
      _ ≤ 4 * (2 * A) ^ α * (2 * H) ^ (1 - α) *
            (4 * Real.pi * (ρ + ‖x‖) ^ ((α * (1 - α) - 3) + 3)
              / ((α * (1 - α) - 3) + 3)) :=
          mul_le_mul_of_nonneg_left (setIntegral_ball_zero_norm_sub_rpow_le x hρ hs) hKnn
      _ = 4 * (2 * A) ^ α * (2 * H) ^ (1 - α) *
            (4 * Real.pi * (ρ + ‖x‖) ^ (α * (1 - α)) / (α * (1 - α))) := by
          rw [show α * (1 - α) - 3 + 3 = α * (1 - α) from by ring]
  -- the shape term
  have hshape : ‖(4 * Real.pi / 3) • crossL (g x)‖ ≤ (4 * Real.pi / 3) * A := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc (4 * Real.pi / 3) * ‖crossL (g x)‖ ≤ (4 * Real.pi / 3) * ‖g x‖ :=
          mul_le_mul_of_nonneg_left (norm_crossL_le _) (by positivity)
      _ ≤ (4 * Real.pi / 3) * A := mul_le_mul_of_nonneg_left (hbdd x) (by positivity)
  have hLHS : Work.CoreResiduals.BiotSavart.bsDerivCLM g ρ x
      = (∫ a in Metric.ball (0 : Work.LWP.R3) ρ, bsIntegrand g x a)
        + (4 * Real.pi / 3) • crossL (g x) := rfl
  rw [hLHS]
  calc ‖(∫ a in Metric.ball (0 : Work.LWP.R3) ρ, bsIntegrand g x a)
        + (4 * Real.pi / 3) • crossL (g x)‖
      ≤ ‖∫ a in Metric.ball (0 : Work.LWP.R3) ρ, bsIntegrand g x a‖
        + ‖(4 * Real.pi / 3) • crossL (g x)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hIntBound hshape

end Work.CoreResiduals.BiotSavart

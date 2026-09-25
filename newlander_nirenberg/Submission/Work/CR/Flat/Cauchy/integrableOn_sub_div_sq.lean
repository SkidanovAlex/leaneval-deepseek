import Mathlib
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open MeasureTheory Set Metric

/-- For a `C¹` function `F` on `ℂ` the function `w ↦ (F w - F 0)/w^2` is integrable on the disc
of radius `R`: on `‖w‖ ≤ R` one has `‖F w - F 0‖ ≤ Λ ‖w‖` for some `Λ` (mean value inequality,
`fderiv ℝ F` is continuous, hence bounded on the compact disc), so the integrand is dominated by
`Λ ‖w‖⁻¹`, which is integrable on a bounded disc in the plane (`1 > -2 = -finrank ℝ ℂ`). -/
theorem integrableOn_sub_div_sq {R : ℝ} {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) :
    MeasureTheory.IntegrableOn (fun w : ℂ => (F w - F 0) / w ^ 2) (Metric.ball (0 : ℂ) R) := by
  -- A `C¹` function is Lipschitz on the compact disc, so `‖F w - F 0‖ ≤ K ‖w‖` there.
  obtain ⟨K, hK⟩ := hF.contDiffOn.exists_lipschitzOnWith (n := 1) (by norm_num)
    (convex_closedBall 0 R) (isCompact_closedBall 0 R)
  -- Measurability of the integrand.
  have hmeas : AEStronglyMeasurable (fun w : ℂ => (F w - F 0) / w ^ 2)
      (volume.restrict (Metric.ball (0:ℂ) R)) :=
    ((hF.continuous.measurable.sub measurable_const).div (measurable_id.pow_const 2)).aestronglyMeasurable
  -- The dominating function `w ↦ K ‖w‖⁻¹` is integrable on the disc (`-1 > -2 = -finrank ℝ ℂ`).
  have hg : Integrable (fun w : ℂ => (K:ℝ) * ‖w‖ ^ (-1:ℝ))
      (volume.restrict (Metric.ball (0:ℂ) R)) :=
    (integrableOn_norm_rpow_ball (ρ := R) (s := -1) (by norm_num)).const_mul (K:ℝ)
  refine hg.mono' hmeas ?_
  filter_upwards [self_mem_ae_restrict measurableSet_ball] with w hw
  have hwcl : w ∈ Metric.closedBall (0:ℂ) R := Metric.ball_subset_closedBall hw
  have hRpos : 0 < R := by
    have := Metric.mem_ball.mp hw
    rw [dist_zero_right] at this
    linarith [norm_nonneg w]
  have h0 : (0:ℂ) ∈ Metric.closedBall (0:ℂ) R := Metric.mem_closedBall_self hRpos.le
  -- The mean value inequality gives `‖F w - F 0‖ ≤ K ‖w - 0‖ = K ‖w‖` on the disc.
  have hlip : ‖F w - F 0‖ ≤ (K:ℝ) * ‖w‖ := by
    have := hK.dist_le_mul w hwcl 0 h0
    rw [dist_eq_norm (F w) (F 0), dist_eq_norm w 0] at this
    simpa using this
  rcases eq_or_ne w 0 with rfl | hw0
  · -- At `w = 0` both sides vanish (`0⁻¹ = 0`).
    simp [Real.zero_rpow (show (-1:ℝ) ≠ 0 by norm_num)]
  · -- For `w ≠ 0`, divide `‖F w - F 0‖ ≤ K ‖w‖` by `‖w‖ ^ 2`.
    rw [norm_div, norm_pow]
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    calc ‖F w - F 0‖ / ‖w‖ ^ 2
        ≤ (K:ℝ) * ‖w‖ / ‖w‖ ^ 2 := div_le_div_of_nonneg_right hlip (by positivity)
      _ = (K:ℝ) * ‖w‖ ^ (-1:ℝ) := by
          rw [Real.rpow_neg_one]
          field_simp

end Work.CR.Flat.Cauchy

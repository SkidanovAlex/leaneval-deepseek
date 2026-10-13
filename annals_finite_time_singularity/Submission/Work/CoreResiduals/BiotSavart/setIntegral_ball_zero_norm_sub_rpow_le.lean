import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.BiotSavart.integral_ball_sub_norm_rpow
import Submission.Work.CoreResiduals.BiotSavart.lintegral_ball_norm_rpow
import Submission.Work.CoreResiduals.BiotSavart.setIntegral_eq_lintegral_of_nonneg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Set
open scoped ENNReal

/-- **Translation invariance of the set Lebesgue integral over an open ball** (centred form):
for any (not necessarily finite) `ℝ≥0∞`-valued function `F`,
`∫⁻_{B(c,r)} F (y - c) = ∫⁻_{B(0,r)} F`. -/
private lemma lintegral_ball_sub_center_eq (c : Work.LWP.R3) (r : ℝ)
    (F : Work.LWP.R3 → ℝ≥0∞) :
    ∫⁻ y in Metric.ball c r, F (y - c) = ∫⁻ z in Metric.ball (0 : Work.LWP.R3) r, F z := by
  classical
  have hs : MeasurableSet (Metric.ball c r) := Metric.isOpen_ball.measurableSet
  have hs0 : MeasurableSet (Metric.ball (0 : Work.LWP.R3) r) :=
    Metric.isOpen_ball.measurableSet
  have hmem : ∀ y : Work.LWP.R3,
      y ∈ Metric.ball c r ↔ y - c ∈ Metric.ball (0 : Work.LWP.R3) r := by
    intro y
    rw [Metric.mem_ball, Metric.mem_ball, dist_eq_norm, dist_eq_norm, sub_zero]
  rw [← lintegral_indicator hs (fun y => F (y - c))]
  have h1 : (fun y => (Metric.ball c r).indicator (fun y => F (y - c)) y)
      = fun y => (Metric.ball (0 : Work.LWP.R3) r).indicator F (y - c) := by
    funext y
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hy : y ∈ Metric.ball c r
    · simp [hy, (hmem y).mp hy]
    · have hy' : y - c ∉ Metric.ball (0 : Work.LWP.R3) r := fun h => hy ((hmem y).mpr h)
      simp [hy, hy']
  rw [h1, lintegral_sub_right_eq_self
    (fun z => (Metric.ball (0 : Work.LWP.R3) r).indicator F z) c]
  rw [lintegral_indicator hs0 F]

/-- **The `B(0,ρ)` norm-power estimate.**  For `ρ ≥ 0`, `s > -3` and any centre `x ∈ ℝ³`,
`∫_{B(0,ρ)} ‖x - a‖^s da ≤ 4π (ρ + ‖x‖)^{s+3} / (s + 3)`.

`B(0,ρ)` is contained in `B(x, ρ + ‖x‖)`; the integrand is a radial power of the distance to its
own singularity, whose integral over a ball is computed by `lintegral_ball_norm_rpow`
(`∫_{B(0,R)} ‖z‖^s = 4π R^{s+3}/(s+3)` for `s > -3`), together with translation invariance
`lintegral_ball_sub_center_eq`.  The conversion between the Bochner integral and the `lintegral`
uses `setIntegral_eq_lintegral_of_nonneg`. -/
theorem setIntegral_ball_zero_norm_sub_rpow_le (x : Work.LWP.R3) {ρ s : ℝ} (hρ : 0 ≤ ρ)
    (hs : -3 < s) :
    ∫ a in Metric.ball (0 : Work.LWP.R3) ρ, ‖x - a‖ ^ s
      ≤ 4 * Real.pi * (ρ + ‖x‖) ^ (s + 3) / (s + 3) := by
  have hs3 : (0 : ℝ) < s + 3 := by linarith
  have hCnn : 0 ≤ 4 * Real.pi * (ρ + ‖x‖) ^ (s + 3) / (s + 3) := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
        (Real.rpow_nonneg (by positivity) _)
    · linarith
  rcases eq_or_lt_of_le hρ with hρ0 | hρpos
  · -- `ρ = 0`: the ball is empty, so the integral vanishes.
    have hball : Metric.ball (0 : Work.LWP.R3) ρ = ∅ :=
      Metric.ball_eq_empty.mpr (le_of_eq hρ0.symm)
    rw [hball, setIntegral_empty]
    exact hCnn
  · -- `ρ > 0`: squeeze the ball `B(0,ρ)` into `B(x, ρ + ‖x‖)` and integrate radially.
    have hRpos : 0 < ρ + ‖x‖ := by linarith [norm_nonneg x]
    have hnn : ∀ a : Work.LWP.R3, 0 ≤ ‖x - a‖ ^ s :=
      fun a => Real.rpow_nonneg (norm_nonneg _) s
    have hmeas : AEStronglyMeasurable (fun a : Work.LWP.R3 => ‖x - a‖ ^ s) volume :=
      (show Measurable (fun a : Work.LWP.R3 => ‖x - a‖ ^ s) by
        measurability).aestronglyMeasurable
    have hsub : Metric.ball (0 : Work.LWP.R3) ρ ⊆ Metric.ball x (ρ + ‖x‖) := by
      intro a ha
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at ha
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖a - x‖ ≤ ‖a‖ + ‖x‖ := norm_sub_le a x
        _ < ρ + ‖x‖ := by linarith
    have hlin : ∫⁻ a in Metric.ball (0 : Work.LWP.R3) ρ, ENNReal.ofReal (‖x - a‖ ^ s)
        ≤ ENNReal.ofReal (4 * Real.pi * (ρ + ‖x‖) ^ (s + 3) / (s + 3)) := by
      calc ∫⁻ a in Metric.ball (0 : Work.LWP.R3) ρ, ENNReal.ofReal (‖x - a‖ ^ s)
          ≤ ∫⁻ a in Metric.ball x (ρ + ‖x‖), ENNReal.ofReal (‖x - a‖ ^ s) :=
            lintegral_mono_set hsub
        _ = ∫⁻ a in Metric.ball x (ρ + ‖x‖), ENNReal.ofReal (‖a - x‖ ^ s) := by
            apply lintegral_congr
            intro a
            rw [norm_sub_rev]
        _ = ∫⁻ z in Metric.ball (0 : Work.LWP.R3) (ρ + ‖x‖), ENNReal.ofReal (‖z‖ ^ s) :=
            lintegral_ball_sub_center_eq x (ρ + ‖x‖) (fun z => ENNReal.ofReal (‖z‖ ^ s))
        _ = ENNReal.ofReal (4 * Real.pi * (ρ + ‖x‖) ^ (s + 3) / (s + 3)) :=
            lintegral_ball_norm_rpow s hs (ρ + ‖x‖) hRpos
    rw [setIntegral_eq_lintegral_of_nonneg measurableSet_ball hmeas hnn]
    exact le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin)
      (le_of_eq (ENNReal.toReal_ofReal hCnn))

end Work.CoreResiduals.BiotSavart

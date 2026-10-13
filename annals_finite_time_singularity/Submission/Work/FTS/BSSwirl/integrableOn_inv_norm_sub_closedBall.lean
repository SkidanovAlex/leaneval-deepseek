import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Submission.Work.FTS.BSSwirl.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Metric
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.BSSwirl

noncomputable section

/-- **The Newtonian kernel is integrable on a ball centred at the origin of `ℝ³`.**

This is the borderline case `s = -1 > -3` of the radial threshold in dimension three: the
weighted integral `∫₀^ρ t^(dim - 1) t^(-1) dt = ∫₀^ρ t dt` converges.  It is the
`integrableOn_ball_of_norm_le_rpow` instance with `C = 1`, `α = 1`. -/
theorem integrableOn_inv_norm_ball_zero (ρ : ℝ) :
    IntegrableOn (fun y : R3 => (‖y‖)⁻¹) (Metric.ball (0 : R3) ρ) volume := by
  have hdim : Module.finrank ℝ R3 = 3 := by
    simp only [R3]
    exact finrank_euclideanSpace_fin
  refine MeasureTheory.integrableOn_ball_of_norm_le_rpow (μ := volume)
    (f := fun y : R3 => (‖y‖)⁻¹) (C := 1) (α := 1) (r := ρ) ?_ ?_ ?_ ?_
  · rw [hdim]; norm_num
  · rw [hdim]; norm_num
  · filter_upwards with x
    rw [norm_inv, norm_norm, Real.rpow_neg_one, one_mul]
  · measurability

/-- **`‖z - c‖⁻¹` is integrable on the closed ball of centre `c` and radius `r` in `ℝ³`.**

The Newtonian kernel is locally integrable in dimension three, and `Metric.closedBall c r` is
bounded; away from `c` the integrand is even bounded.  The proof reduces to the ball centred at
the origin (translation invariance of Lebesgue measure) and then to
`integrableOn_inv_norm_ball_zero`. -/
theorem integrableOn_inv_norm_sub_closedBall (c : Work.FTS.BSSwirl.R3) (r : ℝ) :
    MeasureTheory.IntegrableOn (fun z : Work.FTS.BSSwirl.R3 => (‖z - c‖)⁻¹) (Metric.closedBall c r)
      MeasureTheory.volume := by
  rcases lt_or_ge r 0 with hr | hr
  · -- Degenerate ball: empty.
    rw [Metric.closedBall_eq_empty.mpr hr]
    exact integrableOn_empty
  · -- Translate the ball at the origin of radius `r + 1 > r` to the ball at `c`.
    have hset : (fun x : R3 => x + c) ⁻¹' Metric.ball c (r + 1) = Metric.ball (0 : R3) (r + 1) := by
      ext x
      simp [Metric.mem_ball, dist_eq_norm]
    have hpre : IntegrableOn ((fun z : R3 => (‖z - c‖)⁻¹) ∘ (fun x : R3 => x + c))
        ((fun x : R3 => x + c) ⁻¹' Metric.ball c (r + 1)) volume := by
      rw [hset]
      simpa [Function.comp_def] using integrableOn_inv_norm_ball_zero (r + 1)
    have hc : IntegrableOn (fun z : R3 => (‖z - c‖)⁻¹) (Metric.ball c (r + 1)) volume :=
      (MeasureTheory.MeasurePreserving.integrableOn_comp_preimage
        (measurePreserving_add_right volume c)
        (Homeomorph.measurableEmbedding (Homeomorph.addRight c))
        (f := fun z : R3 => (‖z - c‖)⁻¹) (s := Metric.ball c (r + 1))).mp hpre
    exact hc.mono_set (Metric.closedBall_subset_ball (by linarith))

end

end Work.FTS.BSSwirl

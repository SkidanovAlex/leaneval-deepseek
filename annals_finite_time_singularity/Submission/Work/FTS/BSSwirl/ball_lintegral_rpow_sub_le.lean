import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.CoreResiduals.BiotSavart.lintegral_ball_norm_rpow
import Submission.Work.CoreResiduals.BiotSavart.radial_rpow_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSSwirl

open MeasureTheory Set

/-- **Translation invariance of the set `lintegral` over an open ball**, in the centred
form: for any `ℝ≥0∞`-valued `F`, `∫⁻_{B(c,r)} F (y - c) = ∫⁻_{B(0,r)} F`.  The map
`y ↦ y - c` is measure preserving and carries `B(c,r)` onto `B(0,r)`. -/
private lemma lintegral_ball_sub_center_eq (c : R3) (r : ℝ) (F : R3 → ENNReal) :
    ∫⁻ y in Metric.ball c r, F (y - c) = ∫⁻ z in Metric.ball (0 : R3) r, F z := by
  classical
  have hs : MeasurableSet (Metric.ball c r) := Metric.isOpen_ball.measurableSet
  have hs0 : MeasurableSet (Metric.ball (0 : R3) r) := Metric.isOpen_ball.measurableSet
  have hmem : ∀ y : R3, y ∈ Metric.ball c r ↔ y - c ∈ Metric.ball (0 : R3) r := by
    intro y
    rw [Metric.mem_ball, Metric.mem_ball, dist_eq_norm, dist_eq_norm, sub_zero]
  rw [← lintegral_indicator hs (fun y => F (y - c))]
  have h1 : (fun y => (Metric.ball c r).indicator (fun y => F (y - c)) y)
      = fun y => (Metric.ball (0 : R3) r).indicator F (y - c) := by
    funext y
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hy : y ∈ Metric.ball c r
    · simp [hy, (hmem y).mp hy]
    · have hy' : y - c ∉ Metric.ball (0 : R3) r := fun h => hy ((hmem y).mpr h)
      simp [hy, hy']
  rw [h1, lintegral_sub_right_eq_self
    (fun z => (Metric.ball (0 : R3) r).indicator F z) c]
  rw [lintegral_indicator hs0 F]

theorem ball_lintegral_rpow_sub_le {s : ℝ} (hs : -3 < s) (c : Work.FTS.BSSwirl.R3) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ y in Metric.ball c ρ, ENNReal.ofReal (‖c - y‖ ^ s)
      ≤ ENNReal.ofReal (4 * Real.pi * ρ ^ (s + 3) / (s + 3)) := by
  -- `‖c - y‖ = ‖y - c‖`, so the integrand is a function of `y - c`.
  have hswap : (fun y : R3 => ENNReal.ofReal (‖c - y‖ ^ s))
      = fun y : R3 => ENNReal.ofReal (‖y - c‖ ^ s) := by
    funext y
    rw [norm_sub_rev]
  rw [hswap]
  -- translate the ball to the origin
  rw [lintegral_ball_sub_center_eq c ρ (fun z : R3 => ENNReal.ofReal (‖z‖ ^ s))]
  -- and evaluate the radial power integral
  exact le_of_eq (Work.CoreResiduals.BiotSavart.lintegral_ball_norm_rpow s hs ρ hρ)

end Work.FTS.BSSwirl

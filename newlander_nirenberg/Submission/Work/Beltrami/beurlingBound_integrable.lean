import Mathlib
import Submission.Work.Beltrami.beurlingVAux

namespace Work.Beltrami

open MeasureTheory Set

/-- `w ↦ ‖w‖ ^ s` is integrable on any closed ball of `ℂ` as soon as `s > -2`.  This is
`Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball` (stated there for open balls) transferred to
closed balls, which is what the definition of `beurlingBound` uses. -/
private lemma integrableOn_norm_rpow_closedBall {ρ s : ℝ} (hs : -2 < s) :
    IntegrableOn (fun w : ℂ => ‖w‖ ^ s) (Metric.closedBall (0 : ℂ) ρ) volume := by
  refine (Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball (ρ := max ρ 0 + 1) (s := s)
    hs).mono_set ?_
  intro w hw
  rw [Metric.mem_closedBall, dist_zero_right] at hw
  rw [Metric.mem_ball, dist_zero_right]
  linarith [le_max_left ρ (0 : ℝ), norm_nonneg w]

/-- The Beurling majorant `beurlingBound α K L M R z` is integrable: it is a sum of three terms,
the first two supported on the fixed ball of radius `1/2` (where `‖w‖ ^ (α - 2)` and `‖w‖⁻¹` are
integrable in dimension two, since `α - 2 > -2` when `α > 0`) and the third a constant times the
indicator of the compact ball of radius `max 1 (R + ‖z‖ + 2)`. -/
theorem beurlingBound_integrable {α K L M R : ℝ} (hα : 0 < α) (z : ℂ) :
    MeasureTheory.Integrable (fun w : ℂ => beurlingBound α K L M R z w)
      MeasureTheory.volume := by
  have hα2 : (-2 : ℝ) < α - 2 := by linarith
  -- The first term: `|K| * ‖w‖ ^ (α - 2)` on the ball of radius `1/2`.
  have h1 : IntegrableOn (fun w : ℂ => ‖w‖ ^ (α - 2))
      (Metric.closedBall (0 : ℂ) (1 / 2)) volume :=
    integrableOn_norm_rpow_closedBall hα2
  have hA : MeasureTheory.Integrable (fun w : ℂ =>
      |K| * (Metric.closedBall (0 : ℂ) (1 / 2)).indicator
        (fun w => ‖w‖ ^ (α - 2)) w) MeasureTheory.volume :=
    (IntegrableOn.integrable_indicator h1 Metric.isClosed_closedBall.measurableSet).const_mul |K|
  -- The second term: `|L| * ‖w‖⁻¹` on the same ball (`-2 < -1`).
  have h2 : IntegrableOn (fun w : ℂ => ‖w‖ ^ (-1 : ℝ))
      (Metric.closedBall (0 : ℂ) (1 / 2)) volume :=
    integrableOn_norm_rpow_closedBall (by norm_num)
  have hB : MeasureTheory.Integrable (fun w : ℂ =>
      |L| * (Metric.closedBall (0 : ℂ) (1 / 2)).indicator
        (fun w => ‖w‖ ^ (-1 : ℝ)) w) MeasureTheory.volume :=
    (IntegrableOn.integrable_indicator h2 Metric.isClosed_closedBall.measurableSet).const_mul |L|
  -- The third term: a constant on the closed ball of radius `max 1 (R + ‖z‖ + 2)`, which is
  -- compact and hence of finite measure.
  have h3 : IntegrableOn (fun _ : ℂ => (1 : ℝ))
      (Metric.closedBall (0 : ℂ) (max 1 (R + ‖z‖ + 2))) volume :=
    integrableOn_const (C := (1 : ℝ))
      (ne_of_lt (MeasureTheory.measure_closedBall_lt_top (μ := volume))) (by simp)
  have hC : MeasureTheory.Integrable (fun w : ℂ =>
      8 * (|L| + |M| + 1) * (Metric.closedBall (0 : ℂ) (max 1 (R + ‖z‖ + 2))).indicator
        (fun _ : ℂ => (1 : ℝ)) w) MeasureTheory.volume :=
    (IntegrableOn.integrable_indicator h3 Metric.isClosed_closedBall.measurableSet).const_mul
      (8 * (|L| + |M| + 1))
  have hsum : MeasureTheory.Integrable (fun w : ℂ =>
      |K| * (Metric.closedBall (0 : ℂ) (1 / 2)).indicator (fun w => ‖w‖ ^ (α - 2)) w
      + |L| * (Metric.closedBall (0 : ℂ) (1 / 2)).indicator (fun w => ‖w‖ ^ (-1 : ℝ)) w
      + 8 * (|L| + |M| + 1)
          * (Metric.closedBall (0 : ℂ) (max 1 (R + ‖z‖ + 2))).indicator
              (fun _ : ℂ => (1 : ℝ)) w) MeasureTheory.volume :=
    (hA.add hB).add hC
  refine hsum.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [beurlingBound]

end Work.Beltrami

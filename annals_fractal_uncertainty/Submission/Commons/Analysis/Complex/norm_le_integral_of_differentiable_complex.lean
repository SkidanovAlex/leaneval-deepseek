import Mathlib
import Submission.Commons.Analysis.Complex.meanValue_polydisc
import Submission.Commons.Analysis.Complex.analyticAt_of_differentiableOn_closedBall

namespace Commons.Analysis.Complex

/-- A globally complex-differentiable function on `Fin d → ℂ` is analytic, hence satisfies the
mean-value (subharmonicity) inequality over any polydisc. -/
theorem norm_le_integral_of_differentiable_complex {d : ℕ} {g : (Fin d → ℂ) → ℂ}
    (hg : Differentiable ℂ g) {z : Fin d → ℂ} {r : ℝ} (hr : 0 < r) :
    ‖g z‖ ^ 2 ≤ (MeasureTheory.volume (Metric.closedBall z r)).toReal⁻¹ *
      ∫ w in Metric.closedBall z r, ‖g w‖ ^ 2
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) := by
  have hana : AnalyticOnNhd ℂ g (Metric.closedBall z r) := fun x _ =>
    analyticAt_of_differentiableOn_closedBall (R := 1) one_pos
      (hg.differentiableOn)
  exact meanValue_polydisc hr hana

end Commons.Analysis.Complex

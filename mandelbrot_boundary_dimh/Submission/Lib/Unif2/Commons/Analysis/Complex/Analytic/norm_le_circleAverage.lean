import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Lib.Unif2.Commons.Analysis.Complex.circleAverage_norm_le

set_option linter.unusedVariables false

namespace Commons.Analysis.Complex.Analytic

/-- **Mean value inequality for the modulus of a holomorphic function.**
If `f` is holomorphic on an open set `Ω`, `p ∈ Ω` and the closed ball `closedBall p r`
is contained in `Ω` (with `r > 0`), then `‖f p‖` is bounded by the circle average of
`‖f ·‖` over the circle centred at `p` of radius `r`.

This is the classical mean-value property: `f p` equals the circle average of `f`
(`DiffContOnCl.circleAverage`), and the norm of an average is at most the average of
the norms (`Commons.Analysis.Complex.circleAverage_norm_le`). -/
theorem norm_le_circleAverage {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hf : ∀ z ∈ Ω, AnalyticAt ℂ f z) :
    ∀ p ∈ Ω, ∀ r : ℝ, 0 < r → Metric.closedBall p r ⊆ Ω →
      ‖f p‖ ≤ Real.circleAverage (fun z : ℂ => ‖f z‖) p r := by
  intro p hp r hr hsub
  have hcontΩ : ContinuousOn f Ω := fun z hz => (hf z hz).continuousAt.continuousWithinAt
  have hdiff : DiffContOnCl ℂ f (Metric.ball p |r|) := by
    constructor
    · intro z hz
      rw [abs_of_pos hr] at hz
      have hzΩ : z ∈ Ω := hsub (Metric.ball_subset_closedBall hz)
      exact (hf z hzΩ).differentiableWithinAt
    · rw [abs_of_pos hr, closure_ball p hr.ne']
      exact hcontΩ.mono hsub
  have hmean : Real.circleAverage f p r = f p := hdiff.circleAverage
  calc ‖f p‖ = ‖Real.circleAverage f p r‖ := by rw [hmean]
    _ ≤ Real.circleAverage (fun z : ℂ => ‖f z‖) p r :=
        Commons.Analysis.Complex.circleAverage_norm_le f p r

end Commons.Analysis.Complex.Analytic
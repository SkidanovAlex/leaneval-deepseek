import Mathlib
import Submission.Work.Drive.UmlaufSetup

namespace Work.Drive

/-- The plane curve `t ↦ γ (Circle.exp t)` is `2π`-periodic.

`Circle.exp (t + 2π) = Circle.exp t` is exactly `Circle.periodic_exp t`, so the result follows
by applying `γ`. -/
theorem curve_periodic (γ : Circle → ℝ × ℝ) (t : ℝ) :
    Work.Drive.curve γ (t + 2 * Real.pi) = Work.Drive.curve γ t := by
  simp only [curve]
  rw [Circle.periodic_exp t]

end Work.Drive

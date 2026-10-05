import Mathlib
import Submission.Work.RPB.Port.Drive.UmlaufSetup

namespace Work.RPB.Port.Drive

/-- The plane curve `t ↦ γ (Circle.exp t)` is `2π`-periodic.

`Circle.exp (t + 2π) = Circle.exp t` is exactly `Circle.periodic_exp t`, so the result follows
by applying `γ`. -/
theorem curve_periodic (γ : Circle → ℝ × ℝ) (t : ℝ) :
    Work.RPB.Port.Drive.curve γ (t + 2 * Real.pi) = Work.RPB.Port.Drive.curve γ t := by
  simp only [curve]
  rw [Circle.periodic_exp t]

end Work.RPB.Port.Drive

import Mathlib
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.psi1_contDiff_omega

namespace Work.Asymptotics

open scoped Topology

/-- The complexified regularising factor `x ↦ ((psi1 x : ℝ) : ℂ)` is smooth (`C^∞`).

This is the `C^∞` (rather than `C^ω`) formulation of
`Work.Asymptotics.psi1_contDiff_omega`: the inclusion of differentiability classes
`∞ ≤ ω` in `WithTop ℕ∞` downgrades the analytic statement to a smooth one. -/
theorem psi1_contDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ => ((psi1 x : ℝ) : ℂ)) :=
  psi1_contDiff_omega.of_le le_top

end Work.Asymptotics

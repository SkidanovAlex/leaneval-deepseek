import Mathlib
import Submission.Work.BMF.VKdenom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The cost function for the Vinogradov–Korobov circle estimate

`Work.BMF.ArcCost A B σ τ R` is the right-hand side of the circle-integral bound
`Work.BMF.zeta_circle_arc_cost`: with `s(θ) = σ + iτ + R e^{iθ}`,

`∫₀^{2π} cos θ · log ‖ζ(s(θ))‖ dθ ≥ - ArcCost A B σ τ R`.

It is the sum of the "right-arc" gain `-8 log(2/(σ-1))`, the growth-bound cost
`8 B R^{3/2}(log(|τ|+3)+1) + 8(log(log(|τ|+3)+1)+1)`, and the prefactor cost `4 log A`.
-/

namespace Work.BMF

open scoped Real

/-- Right-hand side of the `cos θ`-weighted circle-integral lower bound for `log ‖ζ‖`. -/
noncomputable def ArcCost (A B σ τ R : ℝ) : ℝ :=
  8 * Real.log (2 / (σ - 1)) + 4 * Real.log A
    + 8 * B * R ^ (3 / 2 : ℝ) * (Real.log (|τ| + 3) + 1)
    + 8 * (Real.log (Real.log (|τ| + 3) + 1) + 1) + 8

end Work.BMF

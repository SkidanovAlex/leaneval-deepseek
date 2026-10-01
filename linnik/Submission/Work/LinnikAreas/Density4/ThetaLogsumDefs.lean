import Mathlib

/-!
# Definitions for `thetaDiag_logsum_core`

The integral-comparison lemma `thetaDiag_logsum_core` concerns the function
`f t = (log t + 1) * t^(σ-1) * exp (-t/A)`, written as the product of the increasing
weight `tgW t = log t + 1` and the antitone (and convex, for `σ ≤ 1`) factor
`tgH σ A t = t^(σ-1) * exp (-t/A)`.
-/

namespace Work.LinnikAreas.Density4

open scoped BigOperators
noncomputable section

/-- The antitone envelope `t^(σ-1) * exp (-t/A)`. -/
def tgH (σ A : ℝ) (t : ℝ) : ℝ := t^(σ - 1) * Real.exp (-t / A)

/-- The increasing weight `log t + 1`. -/
def tgW (t : ℝ) : ℝ := Real.log t + 1

/-- The full integrand/summand `(log t + 1) * t^(σ-1) * exp (-t/A)`. -/
def tgF (σ A : ℝ) (t : ℝ) : ℝ := (Real.log t + 1) * (t^(σ - 1) * Real.exp (-t / A))

/-- `tgF` is the product of `tgW` and `tgH`. -/
lemma tgF_eq (σ A t : ℝ) : tgF σ A t = tgW t * tgH σ A t := rfl

/-- The "defect" of `tgW` on `[n, n+1]`:
`tgEta n = ∫_n^{n+1} (log t + 1 - (log n + 1)) dt = (n+1) * log (1 + 1/n) - 1`. -/
def tgEta (n : ℕ) : ℝ := ((n : ℝ) + 1) * Real.log (1 + 1 / (n : ℝ)) - 1

end

end Work.LinnikAreas.Density4

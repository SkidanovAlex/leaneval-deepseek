import Mathlib
import Submission.Work.CR.Flat.Polydisc

namespace Work.CR.Flat.Polydisc

open scoped NNReal ENNReal
open MeasureTheory Set

/-- Additivity of the `j`-th flat `∂̄`-operator on `ℂⁿ`
(`dbarCoord j u z = (1/2)(∂_{x_j} + i ∂_{y_j})u(z)`, see
`Submission/Work/CR/Flat/Polydisc.lean`) at points where both functions are
real-differentiable. -/
theorem dbarCoord_add {n : ℕ} (j : Fin n) (u v : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    dbarCoord j (fun w => u w + v w) z = dbarCoord j u z + dbarCoord j v z := by
  have hfd : fderiv ℝ (fun w => u w + v w) z = fderiv ℝ u z + fderiv ℝ v z := by
    rw [show (fun w => u w + v w) = u + v from rfl, fderiv_add hu hv]
  simp only [dbarCoord, hfd, add_apply]
  ring

end Work.CR.Flat.Polydisc

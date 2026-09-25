import Mathlib
import Submission.Work.CR.Flat.Polydisc

namespace Work.CR.Flat.Polydisc

open scoped NNReal ENNReal
open MeasureTheory Set

/-- Leibniz rule for the `j`-th flat `∂̄`-operator on `ℂⁿ`
(`dbarCoord j u z = (1/2)(∂_{x_j} + i ∂_{y_j})u(z)`, see
`Submission/Work/CR/Flat/Polydisc.lean`).  Together with `dbarCoord_add` and
`dbarCoord_smul` this is the calculus needed to expand the nonlinear term
`∂̄u = A(u, ∂u)` of the Newlander–Nirenberg perturbation. -/
theorem dbarCoord_mul {n : ℕ} (j : Fin n) (u v : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    dbarCoord j (fun w => u w * v w) z = dbarCoord j u z * v z + u z * dbarCoord j v z := by
  -- Pointwise product of functions is the function-level product.
  have hmul : (fun w => u w * v w) = u * v := by funext w; rw [Pi.mul_apply]
  rw [hmul]
  -- Product rule for the Fréchet derivative, evaluated at the two basis vectors.
  have hfg : fderiv ℝ (u * v) z = u z • fderiv ℝ v z + v z • fderiv ℝ u z := by
    have h := (hu.hasFDerivAt.mul hv.hasFDerivAt).fderiv
    simpa using h
  rw [dbarCoord, hfg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [dbarCoord, dbarCoord]
  ring

end Work.CR.Flat.Polydisc

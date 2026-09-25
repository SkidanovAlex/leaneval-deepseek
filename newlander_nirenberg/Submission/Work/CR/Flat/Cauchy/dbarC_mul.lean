import Mathlib
import Submission.Work.CR.Flat.Cauchy

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open MeasureTheory Set

/-- The flat `∂̄`-operator on `ℂ` (`dbarC u z = (1/2)(∂_x u z + i ∂_y u z)`, see
`Submission/Work/CR/Flat/Cauchy.lean`) satisfies the Leibniz rule, i.e. the
`(0,1)`-part of the derivative of a product:
`∂̄(f·g) = ∂̄f·g + f·∂̄g`.  This is the basic calculus input for the nonlinear
term of the Newlander–Nirenberg perturbation. -/
theorem dbarC_mul (f g : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    dbarC (fun w => f w * g w) z = dbarC f z * g z + f z * dbarC g z := by
  -- Pointwise product of functions is the function-level product.
  have hmul : (fun w => f w * g w) = f * g := by funext w; rw [Pi.mul_apply]
  rw [hmul]
  -- Product rule for the Fréchet derivative, evaluated at the two basis vectors.
  have hfg : fderiv ℝ (f * g) z
      = f z • fderiv ℝ g z + g z • fderiv ℝ f z := by
    have h := (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv
    simpa using h
  rw [dbarC, hfg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [dbarC, dbarC]
  ring

end Work.CR.Flat.Cauchy

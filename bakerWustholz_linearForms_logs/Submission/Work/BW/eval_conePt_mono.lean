import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.subgroup_rayDegAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Evaluation of the monomial `mono N d b = ∏ᵢ X_{i,1}^{bᵢ}X_{i,0}^{dᵢ-bᵢ}` at the cone point `conePt N y` (which sends `X_{i,0} ↦ 1`, `X_{i,1} ↦ yᵢ`): the monomial character `∏ᵢ yᵢ^{bᵢ}`. -/
theorem eval_conePt_mono (N : ℕ) (d : Fin (N + 1) →₀ ℕ) (b : Fin (N + 1) → ℕ) (y : Fin (N + 1) → ℂ) :
    MvPolynomial.eval (conePt N y) (mono N d b) = ∏ i, y i ^ (b i) := by
  simp [mono, conePt]

end Work.BW

import Mathlib
import Submission.Work.Haupt.jtp_defs

/-!
# `Φ`, the theta-series side of the Jacobi triple product

The lemma `Work.Haupt.Phi_differentiableOn` (in `Submission.Work.Haupt.Phi_differentiableOn`)
is stated with a function `Phi` which — when that request was written — had no definition
anywhere in the workspace.  This module supplies the definition, following the convention of
`Submission.Work.Haupt.psi_defs` (the `Psi` side of the same batch of requests), where
`Psi x = jtpLHS x` is the *product* side:

* `Phi x = jtpTheta x` is the *theta series* side `z ↦ ∑' n : ℤ, x^(n^2) * z^n` of the
  Jacobi triple product, and
* `Psi x = jtpLHS x` is the product side
  `z ↦ ∏' n : ℕ, (1 - x^(2(n+1))) * (1 + x^(2n+1) z) * (1 + x^(2n+1)/z)`.

Both satisfy the `q`-difference equation `F (x^2 z) = (x z)⁻¹ F z` on `ℂ \ {0}`
(`Work.Haupt.Phi_functional`, `Work.Haupt.Psi_functional`), and both are holomorphic there
(`Work.Haupt.Phi_differentiableOn`, `Work.Haupt.Psi_differentiable`); these are the two
inputs of the rigidity argument proving Jacobi's triple product
(`Work.Haupt.jtp_rigidity`, `Work.Haupt.jacobi_triple_product`).
-/

namespace Work.Haupt

noncomputable section

open scoped BigOperators

/-- The theta series side of the Jacobi triple product, as a function of the second variable:
`Phi x = jtpTheta x = z ↦ ∑' n : ℤ, x^(n^2) * z^n`. -/
noncomputable def Phi (x : ℂ) : ℂ → ℂ := jtpTheta x

/-- Unfolding `Phi`. -/
@[simp] lemma Phi_apply (x z : ℂ) : Phi x z = jtpTheta x z := rfl

end

end Work.Haupt

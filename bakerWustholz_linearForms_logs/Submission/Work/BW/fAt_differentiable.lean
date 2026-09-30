import Mathlib
import Submission.Work.BW.DefsAC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! ## `z ↦ fAt ℓ P z` is entire

`fAt ℓ P z = P(z, e^{zℓ₁}, …, e^{zℓ_r})` is a complex polynomial in the
coordinate functions `z, e^{zℓ₁}, …, e^{zℓ_r}`, hence differentiable.

The auxiliary statement below is proved by induction on the multivariate
polynomial: constants and the sums/monomial-multiplications that
`MvPolynomial.induction_on` generates are assembled from
`Differentiable.const`, `.add` and `.mul`, while each coordinate function of
`ptC ℓ ·` is either the identity or `z ↦ exp (z * ℓ i)`. -/

theorem fAt_differentiable {r : ℕ} (ℓ : Fin r → ℂ) (P : MvPolynomial (Fin (r + 1)) ℂ) :
    Differentiable ℂ (fun z => fAt ℓ P z) := by
  have key : ∀ Q : MvPolynomial (Fin (r + 1)) ℂ,
      Differentiable ℂ (fun z => MvPolynomial.eval (ptC ℓ z) Q) := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C a => simp only [MvPolynomial.eval_C]; fun_prop
    | add p q hp hq => simp only [map_add]; fun_prop (disch := assumption)
    | mul_X p n hp =>
      have hn : Differentiable ℂ (fun z => ptC ℓ z n) := by
        induction n using Fin.cases with
        | zero => simp only [ptC, Fin.cons_zero]; fun_prop
        | succ j => simp only [ptC, Fin.cons_succ]; fun_prop
      simp only [map_mul, MvPolynomial.eval_X]
      fun_prop (disch := assumption)
  exact key P

end Work.BW

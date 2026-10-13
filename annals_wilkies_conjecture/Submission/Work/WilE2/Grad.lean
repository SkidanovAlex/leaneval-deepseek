/-
  Work.WilE2 — area E2.  The gradient of an EA polynomial, and the bridge between the
  symbolic derivative `ESys.d` and the Fréchet derivative of the evaluated function.
-/
import Submission.Work.WilE2.Degree

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open Classical
namespace Work.WilE2

open WilkiesDesign WilkiesDesign.E WilkiesConjecture

variable {n r : ℕ}

/-- The gradient of `Q` along the chain, as a continuous linear functional on `ℝⁿ`:
`dx ↦ ∑ a, ev (d a Q) x * dx a`. -/
def ESys.grad (S : ESys n r) (Q : EPoly n r) (x : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ a : Fin n, (S.ev (S.d a Q) x) • ContinuousLinearMap.proj a

theorem ESys.grad_apply (S : ESys n r) (Q : EPoly n r) (x v : Fin n → ℝ) :
    S.grad Q x v = ∑ a : Fin n, S.ev (S.d a Q) x * v a := by
  simp only [ESys.grad, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- The derivative of the `i`-th component of the system map is the `i`-th row. -/
def ESys.jacRow (S : ESys n r) (F : Fin n → EPoly n r) (x : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => S.grad (F i) x

end Work.WilE2

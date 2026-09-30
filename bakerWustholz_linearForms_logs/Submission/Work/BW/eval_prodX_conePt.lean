import Mathlib
import Submission.Work.BW.DefsB

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Evaluating the product of `X_{i1}^{a i} X_{i0}^{b i}` (`i ≥ 1`) at the cone point over the
affine point `y` gives `∏ i, y_{i+1}^{a i}` (the `X_{i0}` factors evaluate to `1`). -/
theorem eval_prodX_conePt {N : ℕ} (a b : Fin N → ℕ) (y : Fin (N + 1) → ℂ) :
    MvPolynomial.eval (conePt N y)
      (∏ i : Fin N, MvPolynomial.X ((i.succ : Fin (N + 1)), 1) ^ (a i) *
        MvPolynomial.X ((i.succ : Fin (N + 1)), 0) ^ (b i))
      = ∏ i : Fin N, (y i.succ) ^ (a i) := by
  simp [conePt]

end Work.BW

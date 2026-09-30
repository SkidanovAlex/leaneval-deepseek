import Mathlib
import Submission.Work.BW.subIdealDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Evaluation formula for `charEval`: the character `charEval x` sends the group-algebra
element `q` to the sum over its support of `q.coeff w * ∏ j, (x j : ℂ) ^ (w j)`.
(Here `Laur m = AddMonoidAlgebra ℂ (Fin m → ℤ)` and `charEval x` is defined in
`Submission.Work.BW.subIdealDefs` via `AddMonoidAlgebra.lift`.) -/
lemma charEval_sum {m : ℕ} (x : Fin m → ℂˣ) (q : Laur m) :
    charEval x q = ∑ w ∈ q.coeff.support, q.coeff w * ∏ j, (x j : ℂ) ^ (w j) := by
  rw [charEval, AddMonoidAlgebra.lift_apply]
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl ?_
  intro w _
  rw [smul_eq_mul]
  congr 1
  simp [Units.coeHom_apply, map_prod, Units.val_zpow_eq_zpow_val]

end Work.BW

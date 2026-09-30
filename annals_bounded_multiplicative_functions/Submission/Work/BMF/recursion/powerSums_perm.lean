import Mathlib
import Submission.Work.BMF.recursion.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.recursion

/-- The moment vector is invariant under permutation of the coordinates of a tuple: for
`σ : Equiv.Perm (Fin S)` and `x : Tup S X`,
`powerSums k (fun s => x (σ s)) = powerSums k x`.

Route: each component is a sum over `Fin S` of `((x (σ s)).1)^j`, which is the same as the sum over
`s` of `((x s).1)^j` by reindexing with the equivalence `σ` (`Equiv.sum_comp`/`Fintype.sum_equiv`). -/
theorem powerSums_perm (k S X : ℕ) (σ : Equiv.Perm (Fin S)) (x : Tup S X) :
    Submission.Vinogradov.powerSums k (fun s => x (σ s)) = Submission.Vinogradov.powerSums k x := by
  funext j
  simp only [Submission.Vinogradov.powerSums]
  congr 1
  exact Equiv.sum_comp σ (fun i => (x i).1 ^ j.val)

end Work.BMF.recursion

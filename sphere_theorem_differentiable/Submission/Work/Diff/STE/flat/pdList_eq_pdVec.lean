import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

/-- `pdVec` is `pdList` re-indexed by `Fin`: the list of directions `q` is recovered from the
function `i ↦ q.get i` by `List.ofFn_getElem`. -/
theorem pdList_eq_pdVec {n : ℕ} (q : List (Fin n)) (f : (Fin n → ℝ) → ℂ) :
    Work.Diff.STE.pdList q f = Work.Diff.STE.pdVec q.length (fun i : Fin q.length => q.get i) f := by
  rw [Work.Diff.STE.pdVec]
  congr 1
  simp

end Work.Diff.STE.flat

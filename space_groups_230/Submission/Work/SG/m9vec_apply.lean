import Mathlib
import Submission.Work.SG.SGprelude

namespace Work.SG

/-- The flat matrix-vector product, componentwise. -/
theorem m9vec_apply (a : List ℤ) (v : List ℚ) (i : Fin 3) :
    (m9vec a v).getD i.val 0 =
      ((List.finRange 3).map fun k => (a.getD (3 * i.val + k.val) 0 : ℚ) * v.getD k.val 0).sum := by
  fin_cases i <;> simp [m9vec, List.finRange, List.range_succ]

end Work.SG

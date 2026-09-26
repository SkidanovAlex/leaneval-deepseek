import Mathlib
import Submission.Work.SG.SGsepDefs

namespace Work.SGsep

open Work.SG

set_option maxRecDepth 100000

/-- The affine-class index stored for a representative is a genuine index of `Fin 219`
(`Data.affIdx k = (sgDataList.getD k (0,1,[],0)).2.2.2`).  A finite check over
`Data.sgDataList` (all 230 entries have fourth component `≤ 218`): `k` is a variable so a bare
`decide` fails, but e.g. `(List.range 230).all (fun j => Data.affIdx j < 219) = true` by
`decide +kernel` plus `List.all_eq_true` at `k.val` works (or `fin_cases k <;> decide`).
Needed to deduce `sgAffClass k = sgAffClass l` from the `% 219` definition of `sgAffClass`. -/
theorem affIdx_lt (k : Fin 230) : Data.affIdx k < 219 := by
  have h : (List.range 230).all (fun j => decide (Data.affIdx j < 219)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h k.val (List.mem_range.mpr k.isLt))

end Work.SGsep

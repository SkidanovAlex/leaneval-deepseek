import Mathlib
import Submission.Work.SG.SGsepDefs
import Submission.Work.SGsep.affIdx_lt

namespace Work.SGsep

open Work.SG

set_option maxRecDepth 100000

/-- Representatives with the same affine-class index lie in the same arithmetic class:
`Data.affIdx` takes 219 values and the 11 collisions are the enantiomorphic (merge) pairs, which
are same-class.  A finite check over the 230 × 230 index pairs
(`(List.range 230).all (fun i => (List.range 230).all (fun j => !(affIdx i == affIdx j) || (repClass i == repClass j)))`,
`decide`-able on flat data). -/
theorem repClass_eq_of_affIdx_eq {k l : Fin 230} (h : Data.affIdx k = Data.affIdx l) :
    Data.repClass k = Data.repClass l := by
  have hcheck :
      (List.finRange 230).all (fun i : Fin 230 =>
        (List.finRange 230).all (fun j : Fin 230 =>
          !(Data.affIdx i == Data.affIdx j) || (Data.repClass i == Data.repClass j))) = true := by
    decide +kernel
  have hk := List.all_eq_true.mp hcheck k (List.mem_finRange k)
  have hl := List.all_eq_true.mp hk l (List.mem_finRange l)
  rw [h] at hl
  simpa [beq_iff_eq] using hl

end Work.SGsep

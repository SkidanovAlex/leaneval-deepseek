import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs
import Submission.Work.ORLyndon.CLDirect.clPi_of
import Submission.Work.ORLyndon.CLDirect.clDelta_mul
import Submission.Work.ORLyndon.CLDirect.clDelta_one

namespace Work.ORLyndon.CLDirect

/-- `φ(1) = 0`. Proof: `rw [clPhi, dif_pos (Subgroup.one_mem _)]`; `map_one`; `clDelta_one`. -/
theorem clPhi_one {X : Type*} [DecidableEq X] {K : Type*} [Field K] {u : FreeGroup X}
    (D : Work.ORLyndon.CLDirect.CLData u) (l : ℕ) :
    Work.ORLyndon.CLDirect.clPhi (K := K) D l 1 = 0 := by
  rw [Work.ORLyndon.CLDirect.clPhi, dif_pos (Subgroup.one_mem _)]
  have h : D.e.symm ⟨1, Subgroup.one_mem (Subgroup.normalClosure ({u} : Set (FreeGroup X)))⟩ = 1 :=
    map_one _
  rw [h]
  exact Work.ORLyndon.CLDirect.clDelta_one D l

end Work.ORLyndon.CLDirect

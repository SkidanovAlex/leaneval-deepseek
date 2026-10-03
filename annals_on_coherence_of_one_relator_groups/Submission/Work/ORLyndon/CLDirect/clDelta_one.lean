import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs
import Submission.Work.ORLyndon.CLDirect.clDelta_mul

namespace Work.ORLyndon.CLDirect

/-- `clDelta 1 = 0`. Reviewer's concrete proof: `simp [clDelta, foxFD_one]` (unfolding `clDelta` turns the goal into `(foxFD 1).sum H = 0`, closed by `foxFD_one` and `Finsupp.sum_zero_index`). -/
theorem clDelta_one {X : Type*} [DecidableEq X] {K : Type*} [Field K] {u : FreeGroup X}
    (D : Work.ORLyndon.CLDirect.CLData u) (l : ℕ) :
    Work.ORLyndon.CLDirect.clDelta (K := K) D l 1 = 0 := by
  simp [Work.ORLyndon.CLDirect.clDelta, Work.ORLyndon.foxFD_one]

end Work.ORLyndon.CLDirect

import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.theta_null_z

open MeasureTheory Filter Topology Set

namespace Work.TMC16Core.Basic

/-- AJ (9.1): the exceptional set of phases is null.  (The collision index ranges over all of
`ℤ`; both tails are handled by the same union bound, and the exact-collision set is
countable.) -/
theorem theta_null (α : ℝ) (hα : Irrational α) :
    MeasureTheory.volume (Work.TMC16Core.Theta α) = 0 :=
  theta_null_z α hα

end Work.TMC16Core.Basic

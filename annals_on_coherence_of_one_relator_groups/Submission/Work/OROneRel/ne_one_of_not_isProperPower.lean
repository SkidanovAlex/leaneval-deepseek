import Mathlib
import Submission.Work.OROneRel.Basic

universe u

namespace Work.OROneRel

theorem ne_one_of_not_isProperPower {α : Type u} {r : FreeGroup α}
    (h : ¬ Work.OROneRel.IsProperPower r) : r ≠ 1 := by
  intro hr
  exact h (hr ▸ isProperPower_one)

end Work.OROneRel

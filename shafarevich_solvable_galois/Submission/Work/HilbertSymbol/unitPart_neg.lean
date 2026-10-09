import Mathlib
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

theorem unitPart_neg (p : ℕ) [Fact p.Prime] (a : ℚˣ) :
    unitPart p (-a) = unitPart p (-1) * unitPart p a := by
  rw [show (-a : ℚˣ) = (-1) * a by simp, unitPart_mul]

end Work.HilbertSymbol

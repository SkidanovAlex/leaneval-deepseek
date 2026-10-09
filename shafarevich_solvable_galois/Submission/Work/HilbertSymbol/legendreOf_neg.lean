import Mathlib
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- `legendreOf p` is a multiplicative character of `ℚˣ`: applying it to `-a` gives the product
of its value on `-1` and on `a`. -/
theorem legendreOf_neg (p : ℕ) [Fact p.Prime] (a : ℚˣ) :
    legendreOf p (-a) = legendreOf p (-1) * legendreOf p a := by
  rw [show (-a : ℚˣ) = -1 * a by simp, legendreOf_mul]

end Work.HilbertSymbol

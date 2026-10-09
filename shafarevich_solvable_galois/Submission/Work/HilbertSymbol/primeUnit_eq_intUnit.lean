import Mathlib
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

theorem primeUnit_eq_intUnit (p : ℕ) [Fact p.Prime] :
    primeUnit p = intUnit (p : ℤ) (by exact_mod_cast (Fact.out : p.Prime).ne_zero) := by
  ext
  simp [primeUnit, intUnit, ratUnit]

end Work.HilbertSymbol

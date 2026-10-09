import Mathlib
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

theorem hilbertSymbolOdd_eq_one_of_padicVal_eq_zero {p : ℕ} [Fact p.Prime] {a b : ℚˣ}
    (ha : padicVal p a = 0) (hb : padicVal p b = 0) : hilbertSymbolOdd p a b = 1 := by
  unfold hilbertSymbolOdd
  rw [ha, hb]
  simp

end Work.HilbertSymbol

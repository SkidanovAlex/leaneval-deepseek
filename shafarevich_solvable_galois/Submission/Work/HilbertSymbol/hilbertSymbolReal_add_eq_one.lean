import Mathlib
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

theorem hilbertSymbolReal_add_eq_one {a b : ℚˣ} (h : (a : ℚ) + (b : ℚ) = 1) :
    hilbertSymbolReal a b = 1 := by
  rw [hilbertSymbolReal_eq_one_iff]
  rintro ⟨ha, hb⟩
  linarith

end Work.HilbertSymbol

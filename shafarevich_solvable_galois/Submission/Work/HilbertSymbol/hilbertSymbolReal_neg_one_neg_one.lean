import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- At the archimedean place, `(-1, -1)_∞ = -1`, since both entries are negative. -/
theorem hilbertSymbolReal_neg_one_neg_one :
    hilbertSymbolReal (-1 : ℚˣ) (-1 : ℚˣ) = -1 := by
  simp [hilbertSymbolReal]

end Work.HilbertSymbol

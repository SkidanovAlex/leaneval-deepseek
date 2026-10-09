import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- The place product of the Hilbert symbols `(a, b ^ 2)_v` is trivial: each local symbol
`(a, b ^ 2)_v` equals `1`, since a square is a norm at every place. -/
theorem placeProduct_sq_right (a b : ℚˣ) : placeProduct a (b ^ 2) = 1 := by
  rw [placeProduct_def]
  simp [hilbertSymbol_sq_right]

end Work.HilbertSymbol

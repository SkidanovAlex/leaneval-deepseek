import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- The place product of the Hilbert symbols `(a ^ 2, b)_v` is trivial: each local symbol
`(a ^ 2, b)_v` equals `1`, since a square is a norm at every place. -/
theorem placeProduct_sq_left (a b : ℚˣ) : placeProduct (a ^ 2) b = 1 := by
  rw [placeProduct_def]
  simp [hilbertSymbol_sq_left]

end Work.HilbertSymbol

import Mathlib
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- The archimedean Hilbert symbol is trivial in its first argument when that argument is a
square: `(a²,b)_∞ = 1`. Indeed `a² > 0` for `a ≠ 0`, so the criterion
`(a,b)_∞ = -1 ↔ a < 0 ∧ b < 0` never applies. -/
theorem hilbertSymbolReal_sq_left (a b : ℚˣ) : hilbertSymbolReal (a ^ 2) b = 1 := by
  rw [hilbertSymbolReal, if_neg]
  rintro ⟨h, _⟩
  have ha : ((a ^ 2 : ℚˣ) : ℚ) = (a : ℚ) ^ 2 := by push_cast; ring
  rw [ha] at h
  nlinarith [sq_nonneg (a : ℚ)]

end Work.HilbertSymbol

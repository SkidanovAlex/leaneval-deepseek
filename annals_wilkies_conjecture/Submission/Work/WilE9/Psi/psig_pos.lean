import Mathlib
import Submission.Work.WilE9.Defs

namespace Work.WilE9.Psi

/-- The denominator `√(1+x²)` of `psig` is strictly positive. -/
theorem sqrt_one_add_sq_pos (x : ℝ) : 0 < Real.sqrt (1 + x ^ 2) :=
  Real.sqrt_pos.2 (by positivity)

/-- `psig` is strictly positive. -/
theorem psig_pos (x : ℝ) : 0 < Work.WilE9.psig x := by
  rw [Work.WilE9.psig]
  exact div_pos one_pos (sqrt_one_add_sq_pos x)

end Work.WilE9.Psi

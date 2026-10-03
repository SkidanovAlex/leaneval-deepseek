/-
# The elementary scales `2^{Log N}` and `2^{d(Log N - k)}`

These two definitions are shared between the symbol estimate `symD_deriv_bound` and the bump-mass
estimates in `A6Mass`.
-/
import Mathlib
import Submission.Work.Analysis.EndVar.Defs

set_option autoImplicit false

namespace Work.KMTPlan.A6

noncomputable section

/-- The continuous scale `2^{Log N}`, `Log N = ⌊log₂ N⌋`. -/
noncomputable def thN (N : ℕ) : ℝ := (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)

/-- The scale `2^{d(Log N - k)}` of the second bump. -/
noncomputable def psN (d N k : ℕ) : ℝ :=
  ((2 : ℝ) ^ d) ^ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) / (2 : ℝ) ^ (d * k)

end

end Work.KMTPlan.A6

import Mathlib

/-!
# The unit complex exponential `ee`

Shared definition of `ee x = exp (2 π i x)`, used by both `lip2IccBasic` and `lip2PlainIW`
(which previously each carried an identical copy, clashing when both are imported).
-/

namespace Work.KMTAreas.A4

/-- The complex exponential `𝐞 (x) = exp (2 π i x)`. -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

end Work.KMTAreas.A4

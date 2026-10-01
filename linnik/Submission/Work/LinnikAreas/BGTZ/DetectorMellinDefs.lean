/-
# Vocabulary for the smoothed Mellin inversion (`DetectorMellin`)

The Mellin/Perron kernel used by the BGTZ detector argument: for `Re s = c > 0` the integral

`(1/2π) ∫_ℝ x^s / (s (s+1)) dt`,   `s = c + it`,

evaluates to `max 0 (1 - 1/x)` for real `x > 0`.  We package the integral as `mellK c x`
(defined for every complex `x`, so that the sum over `n` can be matched directly).

The evaluation itself is `Work.LinnikAreas.BGTZ.DetectorKernel`; it follows from Mathlib's
Mellin inversion theorem `mellinInv_mellin_eq` applied to the tent function `max 0 (1 - u)`,
whose Mellin transform is `1/(s(s+1))`.
-/
import Mathlib

open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.BGTZ

/-- The Mellin kernel `(1/2π) ∫_ℝ x^{c+it}/((c+it)(c+1+it)) dt`. -/
def mellK (c : ℝ) (x : ℂ) : ℂ :=
  (1 / (2 * Real.pi)) * ∫ t : ℝ, x ^ (c + t * Complex.I)
    / ((c + t * Complex.I) * (c + 1 + t * Complex.I))

end Work.LinnikAreas.BGTZ

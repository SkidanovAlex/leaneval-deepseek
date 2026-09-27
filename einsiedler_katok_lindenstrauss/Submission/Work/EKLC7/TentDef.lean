import Mathlib

/-!
# The tent (trapezoid) function, definition file

This file only fixes the *notation*: the tent function that appears in
`Work.EKLC7.TentDetermine` as `Work.EKLC7.tent`, under the name `tentFormula`, so that
lemmas about the tent function can be delegated without importing the main file (which
would create an import cycle).

The body is literally the body of `Work.EKLC7.tent`.
-/

namespace Work.EKLC7

/-- The tent/trapezoid function with rational parameters `a < b` and slope parameter `n`:
it grows linearly from `0` to `1` on `[a, a + 1/n]`, stays `1` up to `b`, and decays
linearly back to `0` on `[b, b + 1/n]`. -/
def tentFormula (a b : ℚ) (n : ℕ) (t : ℝ) : ℝ :=
  max 0 (min 1 (min ((n : ℝ) * (t - a)) (1 + (n : ℝ) * (b - t))))

end Work.EKLC7

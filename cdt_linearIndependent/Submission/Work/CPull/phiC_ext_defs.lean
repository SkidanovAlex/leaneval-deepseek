import Mathlib
import Submission.CDTPlan.InterfacesC

/-!
# CPull — explicit rational inverse of the contour map `psiC`

`lune (c) : ℂ → ℂ` is the explicit inverse (eq. `(firstgobble)` of the paper) of the lune
conformal map `f(z,c) = z((c²+1) + (c²-1)z)/((c²-1) + (c²+1)z)`.  For `c = 23/10`,
`psiC = -(3/4) * lune (23/10)`, so the inverse of `psiC` is `psiF`, the explicit rational
function `w ↦ luneF (-(4/3) w)`.

These definitions are the vocabulary in which the meromorphic-pullback development of area
`CPull` states that `psiC` is injective with nowhere vanishing derivative.
-/

namespace Work.CPull

open Submission.CDTPlan

/-- `γ = (23/10)²`, the value of `c²` for the Theorem C contour. -/
noncomputable def gammaC : ℂ := (((23 / 10 : ℝ) : ℂ)) ^ 2

/-- The explicit rational inverse of `lune (23/10)`: it is the map
`f(z,c) = z((c²+1) + (c²-1)z)/((c²-1) + (c²+1)z)` of the paper with `c = 23/10`. -/
noncomputable def luneF (w : ℂ) : ℂ :=
  w * (1 + gammaC + (gammaC - 1) * w) / ((gammaC - 1) + (1 + gammaC) * w)

/-- The explicit rational inverse of `psiC = -(3/4) * lune (23/10)`. -/
noncomputable def psiF (w : ℂ) : ℂ := luneF (-(4 / 3) * w)

end Work.CPull

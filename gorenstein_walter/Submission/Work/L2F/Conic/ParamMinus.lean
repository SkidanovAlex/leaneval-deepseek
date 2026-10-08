import Mathlib
import Submission.Work.L2F.Defs

/-!
# The rational parametrisation of the conic `a² - d·b² = 1` from the point `(-1,0)`

For a field `F` and `d : F` the conic `C_d = {(a,b) | a² - d·b² = 1}` contains the point
`(-1,0)`.  Every other point of the conic lies on a unique line through `(-1,0)`; if that line has
slope `t`, the second intersection is

`conicMinusParam d t = ((1 + d t²)/(1 - d t²), 2 t/(1 - d t²))`,

and conversely the slope attached to a point `(a,b) ≠ (-1,0)` of the conic is `b/(1 + a)`.

When `d ≠ 0` is not a square in `F`, the denominator `1 - d t²` never vanishes (if `d t² = 1`
with `t ≠ 0` then `d = (t⁻¹)²`, and `t = 0` gives `0 = 1`), so the parametrisation is defined for
all `t : F`.  This is what makes the conic have `q + 1` points.

Nothing here needs a proof, so the file contains the definition only; the statements about it
live in the files next to it.
-/

namespace Work.L2F.Conic

variable {F : Type*} [Field F]

/-- The parametrised point of the conic `a² - d·b² = 1`: the second intersection of the line
through `(-1,0)` of slope `t` with the conic. -/
def conicMinusParam (d : F) (t : F) : F × F :=
  ((1 + d * t ^ 2) / (1 - d * t ^ 2), 2 * t / (1 - d * t ^ 2))

end Work.L2F.Conic

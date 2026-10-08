import Mathlib
import Submission.Work.L2F.Defs

/-!
# The rational parametrisation of the conic `a² + b² = 1`

For a field `F` the conic `C = {(a,b) | a² + b² = 1}` is parametrised by the "slope of the line
through `(0,1)`": the point `(a,b) ≠ (0,1)` corresponds to `t = a/(1-b)`, and the inverse map
sends `t` to `(2t/(t²+1), (t²-1)/(t²+1))`, while `(0,1)` itself corresponds to "`t = ∞`",
represented by `none : Option F`.

The two maps are `conicSlope` (`C → Option F`) and `conicParam` (`Option F → F × F`).  When `-1`
has no square root in `F`, `t² + 1 ≠ 0` for every `t`, so `conicParam` never divides by zero and
the two maps are mutually inverse bijections; this is what makes the conic have `q + 1` points.

Nothing here needs a proof, so this file contains definitions only, and the statements about them
live in the files next to it.
-/

namespace Work.L2F.Conic

/-- The conic `a² + b² = 1` inside `F × F`. -/
def conic (F : Type*) [Field F] : Set (F × F) := {p | p.1 ^ 2 + p.2 ^ 2 = 1}

/-- The inverse parametrisation of the conic `a² + b² = 1` from the point `(0,1)`: `none` stands
for `(0,1)`, and `some t` for `(2t/(t²+1), (t²-1)/(t²+1))`. -/
def conicParam (F : Type*) [Field F] (m : Option F) : F × F :=
  match m with
  | none => (0, 1)
  | some t => (2 * t / (t ^ 2 + 1), (t ^ 2 - 1) / (t ^ 2 + 1))

/-- The slope of the line joining the point `p` of the conic to `(0,1)`, i.e. `p.1/(1 - p.2)`;
`none` when `p = (0,1)`. -/
noncomputable def conicSlope (F : Type*) [Field F] (p : F × F) : Option F := by
  classical
  exact if p.2 = 1 then none else some (p.1 / (1 - p.2))

end Work.L2F.Conic

import Mathlib
import Submission.Work.Mostow.QIDefs

/-!
# The cusp map `cuspPsi`

Vocabulary for the `cuspMap` development.

Given a map `ψ` defined on the horosphere `ξ^⊥` of a boundary point `ξ` (whose image lands in
`η^⊥` for a second boundary point `η`), the *cusp map* pushes the flat coordinate `yc ξ u` of a
point `u` through `ψ` and keeps its Busemann level `lev ξ u`:

`cuspPsi ψ ξ η u = hptOf η (ψ (yc ξ u)) (lev ξ u)`.

It is a map defined on all of `ℍⁿ` (the chart `E n`) which restricts to `ψ` on the level-`1`
horosphere of `ξ` and is used to build the quasi-isometry of the cusp at `ξ` onto the cusp at `η`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

variable {n : ℕ}

/-- The cusp map attached to `ψ`, `ξ`, `η`: keep the level `lev ξ ·`, move the flat coordinate
by `ψ`. -/
noncomputable def cuspPsi (ψ : E n → E n) (ξ η : E n) (u : E n) : E n :=
  hptOf η (ψ (yc ξ u)) (lev ξ u)

end Work.Mostow

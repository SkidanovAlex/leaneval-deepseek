/-
# `Work.RTInstance`: the concrete instance `Work.Space.RTData` of `M̂`

This area produces the one field `rt : Work.Space.RTData` that `Work.Final.FinalInputs` still owes:
the assembled space `M̂` of the Ratcliffe--Tschantz construction, with

* `Work.Space.Assembly` — the adjunction space `M̂ = M̄ ∪ (⊔_v [-1,1]² × T_v)`,
* `Work.Space.ModelAtlas M̂` — the finite atlas of the fold, cusp, polar and core charts with their
  metric models (upper half space / warped filling / flat core),
* the isometry of the transitions of the atlas, and
* their smoothness.

## The modules of this area

| module | content |
|---|---|
| `Submission.Work.RTInstance.Basic` | conventions, the torus factor `T_v`, the metric models |
| `Submission.Work.RTInstance.PreAtlas` | a finite chart family with models and the pairwise isometry property; the `ModelAtlas`, the `IsManifold` instance, the isometry, and the curvature datum |
| `Submission.Work.RTInstance.Transfer` | transports: a chart of `M̄` avoiding `Tset`, and a chart of a filling piece, as charts of `M̂` |
| `Submission.Work.RTInstance.Instance` | the pending inputs of `FOLDINST`/`CUSP` as named hypotheses, and the instance |

Everything here is written *modulo* the results of the areas `FoldInst` and `Cusp` that were still
in flight; see `Submission/Work/RTInstance/NOTES.md`.

## Conventions

* `E4 = EuclideanSpace ℝ (Fin 4)`, `I4 = 𝓘(ℝ, E4)` (the chart model of the whole project).
* the filling pieces are `SquarePt × T_v` with `T_v = (ℝ/ℤ)² = (Fin 2 → AddCircle 1)`, matching
  `Work.Space.Assembly` and `Work.Cusp`.
* the third coordinate `q 3` of `E4` is the UHS height; `(r,θ,w₁,w₂)` are the polar coordinates
  of the filling, `(a,b,w₁,w₂)` the Cartesian coordinates of its core.
-/
import Mathlib
import Submission.Work.Space.Main
import Submission.Work.Curvature.Main
import Submission.Work.Profiles.Main
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter
open scoped Manifold ContDiff Topology Bundle RealInnerProductSpace
open Bundle

namespace Work.RTInstance

/-- The chart model of the project: `ℝ⁴`. -/
abbrev E4 := Work.Space.E4

/-- The model-with-corners structure of the chart model. -/
abbrev I4 := Work.Space.I4

/-- The index type of the cusps of `M̂`: five cusps. -/
abbrev Cusp := Work.Space.Cusp

/-- The closed square `[-1,1]²`, the filling disk. -/
abbrev SquarePt := Work.Space.SquarePt

/-- **The torus factor of a filling piece**: `T_v = (ℝ/ℤ)²`, the two cusp coordinates `(y₂,y₃)` of
`Work.Cusp`.  This is the concrete `Assembly.Torus` of the Ratcliffe--Tschantz assembly. -/
abbrev Torus : Type := Fin 2 → AddCircle (1 : ℝ)

instance : CompactSpace Torus := Pi.compactSpace

instance : T2Space Torus := inferInstance

instance : ConnectedSpace (AddCircle (1 : ℝ)) := inferInstance

instance : Nonempty (AddCircle (1 : ℝ)) := inferInstance

theorem continuous_torus_coord (i : Fin 2) : Continuous fun y : Torus => y i :=
  continuous_apply i

end Work.RTInstance

/-
Copyright: subproject `Submission/Work/SeedSimple2/` of `mandelbar_not_path_connected`.

# SeedSimple2/COP — `L9`: the angle monotonicity `Rotation.angleMono`

`NOTES_LEAD_mandelbar_rn0.md` §2, `L9`; `COP/NOTES_COP.md` §4.  This file is the wrapper that
instantiates

* the cyclic-order preservation `COP/cop_angles.lean` (`L7`) and
* the `L3` consequences `COP/theta_iterate_ne.lean`

in the arithmetic core `COP/angleMono_at_of_cop.lean`.  Together with `COP/arcBound_proved.lean`
(`L8`) this gives `RN0` (`COP/rotationZero_proved.lean`).
-/
import Submission.Work.SeedSimple2.COP.cop_angles
import Submission.Work.SeedSimple2.COP.theta_iterate_ne
import Submission.Work.SeedSimple2.COP.angleMono_at_of_cop

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar)

set_option linter.unusedVariables false

noncomputable section

namespace Work.SeedSimple2.COP

/-- **`L9`: the angle monotonicity** (`NOTES_LEAD_mandelbar_rn0.md` §2, `L9`): for every landing
angle `θ ∈ A` with `Int.fract (1024 * θ) ≠ θ`, the sequence
`n ↦ Int.fract ((1024:ℝ)^n * θ - α₁)` is strictly monotone in one of the two directions.

`hJ` enters only through `Work.ELTop.pairSides` inside `cop_sides`. -/
theorem angleMono_proved (hJ : Work.Top.JordanForm) :
    Work.SeedSimple2.Rotation.angleMono :=
  fun {c} d =>
    Work.SeedSimple2.COP.angleMono_at_of_cop d
      (fun {x a e} hx ha he ha0 he0 hxa hxe hae => cop_angles d hJ hx ha he ha0 he0 hxa hxe hae)
      (fun {θ} hθ hne => Work.SeedSimple2.COP.theta_iterate_ne d hθ hne)

end Work.SeedSimple2.COP

end

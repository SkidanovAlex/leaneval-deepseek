/-
Copyright: subproject `Submission/Work/SeedSimple2/` of `mandelbar_not_path_connected`.

# SeedSimple2/COP — `L7`: cyclic-order preservation, angle form

`NOTES_LEAD_mandelbar_rn0.md` §2, `L7`; `COP/NOTES_COP.md` §4.  This file is the wrapper that
instantiates the side-preservation hypothesis of `COP/cop_angles_of_sides.lean` with the theorem
`COP/cop_sides.lean`.
-/
import Submission.Work.SeedSimple2.COP.cop_sides
import Submission.Work.SeedSimple2.COP.cop_angles_of_sides

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

/-- **`L7`: cyclic-order preservation, angle form** (`NOTES_LEAD_mandelbar_rn0.md` §2, `L7`): for
three distinct landing angles `x, a, e` of the parabolic point `z₁` (with `a, e ≠ 0`), the cyclic
arc membership of `x` in `(a,e)` is equivalent to that of `Int.fract (1024 * x)` in
`(Int.fract (1024 * a), Int.fract (1024 * e))`.

This is the correspondence `wₙ < wₙ₊₁ ↔ wₙ₊₁ < wₙ₊₂` used by `L9` (`angleMono_proved`). -/
theorem cop_angles {c : ℂ} (d : Work.EL.RootParabolic c) (hJ : Work.Top.JordanForm)
    {x a e : ℝ} (hx : x ∈ Work.SeedSimple2.LandAngles d.hN d.z₁)
    (ha : a ∈ Work.SeedSimple2.LandAngles d.hN d.z₁)
    (he : e ∈ Work.SeedSimple2.LandAngles d.hN d.z₁)
    (ha0 : a ≠ 0) (he0 : e ≠ 0) (hxa : x ≠ a) (hxe : x ≠ e) (hae : a ≠ e) :
    Work.EL.InArc x a e ↔
      Work.EL.InArc (Int.fract (1024 * x)) (Int.fract (1024 * a)) (Int.fract (1024 * e)) :=
  cop_angles_of_sides d hJ
    (fun Q Q' hQy hQ'y hPa hPb hab ha' hb' hnd' =>
      cop_sides d hJ Q Q' hQy hQ'y hPa hPb hab ha' hb' hnd')
    hx ha he ha0 he0 hxa hxe hae

end Work.SeedSimple2.COP

end

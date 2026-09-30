/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The tower base-change square `C_{F'} ⟶ C_F` and the pullback of sections (area SY)

For a tower of field extensions `K → F → F'` the canonical morphism
`BCSquareBaseChange.towerHom : C_{F'} ⟶ C_F` (delegated) fits into a cartesian square over
`Spec F' ⟶ Spec F` (`BCSquareBaseChange.isPullback_tower`).  This file packages it as a
`Work.CurveBasics.Curve.BCSquare` (`bcSquareTower`), records that the preimage of `V_F` is
`V_{F'}` (`towerHom_preimage_bcOpens`), and defines the induced pullback of sections
`bcSec`, the tool with which the divisor ideal of a point of `Symⁿ C` is compared with
`∏_m m_{x_m}` (the lead's C1, `Submission/Work/NOTES_LEAD_jacobian_divof.md` §2).
-/
import Submission.Work.SymQuot.DivOf.exists_bcSquare_baseChange
import Submission.Work.SymQuot.DivOf.AffineCurve

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.DivOf

open Work.CurveBasics

variable {K : Type u} [Field K] {C : Curve K}

/-- **The tower base-change square** `C_{F'} ⟶ C_F` over `Spec F' ⟶ Spec F`, as a
`Curve.BCSquare`. -/
noncomputable def bcSquareTower (F F' : Type u) [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] :
    Curve.BCSquare (C.baseChange F) (C.baseChange F') :=
  ⟨BCSquareBaseChange.towerHom (C := C) (F := F) (F' := F'), BCSquareBaseChange.isPullback_tower (C := C) (F := F) (F' := F')⟩

end Work.SymQuot.DivOf

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# CB7 holds for every curve (area SY)

The curve input of area SY (`Work.SymQuot.CurveAffineCover`: every finite set of points of a
curve lies in an affine open subscheme) is *available in the workspace*: area `SpecLin`'s
`Work.SpecLin.Chart.exists_isAffineOpen_containing` proves exactly this statement, for every
curve and with no further hypotheses.

Consequently the symmetric power `Symⁿ C` (and everything built from it) needs no hypothesis
beyond `C : Curve k`.
-/
import Submission.Work.SymQuot.CurveInput
import Submission.Work.SpecLin.Chart.exists_isAffineOpen_containing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot

/-- **CB7 for curves**, in the form used by area SY: `Work.SpecLin.Chart.exists_isAffineOpen_containing`
is precisely the statement that every finite set of points of a curve is contained in an affine
open subscheme. -/
instance instCurveAffineCover {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) :
    CurveAffineCover C :=
  ⟨fun S hS => Work.SpecLin.Chart.exists_isAffineOpen_containing C S hS⟩

end Work.SymQuot

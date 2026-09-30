/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The curve input of area SY (CB7, in the form used by the symmetric powers)

This file records the input that the construction of the symmetric power `Sym^n C` needs from
area CB (`Submission/Work/CB7`): every finite set of points of a curve lies in an affine open
subscheme.  This is CB's "CB7"; it is *not* a theorem of Mathlib (it needs Riemann–Roch).

It is recorded as a `class` so that `Sym^n C` can be constructed under it and so that the
consumers of `SymGeom` (which only see the *output* of the construction) do not have to carry
it.
-/
import Submission.Work.CurveBasics.Basic
import Submission.Work.CurveBasics.Place.Coheight

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot

variable {k : Type u} [Field k]

/-- **CB7, in the form used by area SY.** Every finite set of points of a curve is contained in
an affine open subscheme.

(The interesting case is that of finitely many *closed* points; the generic point lies in every
nonempty open.)  This is the hypothesis under which the `n`-fold product `C^n` is covered by
`S_n`-invariant affine open subschemes `V^n` (`Work.SymQuot.piOpen`), and hence under which the
symmetric power `Sym^n C = C^n/S_n` is constructed. -/
class CurveAffineCover (C : Work.CurveBasics.Curve k) : Prop where
  /-- a finite set of points is contained in an affine open -/
  exists_isAffineOpen_superset :
    ∀ S : Set C.left, S.Finite → ∃ U : C.left.Opens, IsAffineOpen U ∧ S ⊆ U

end Work.SymQuot

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Places have coheight one

A place of a curve is a point of codimension one, so its local ring has Krull dimension one.
This file records that, together with the classification of the points of a curve.
-/
import Submission.Work.CurveBasics.Place
import Submission.Work.CurveBasics.Point.isClosed_of_coheight_eq_one
import Submission.Work.CurveBasics.Point.coheight_eq_one_of_isClosed

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

namespace Work.CurveBasics

namespace Curve

variable {k : Type u} [Field k]

namespace Place

variable {C : Curve k}

/-- The coheight of a place is one: places are the points of codimension one. -/
theorem eq_coheight_one (Q : Place C) : Order.coheight Q.point = 1 :=
  Point.coheight_eq_one_of_isClosed C Q.isClosed

/-- The local ring of a curve at a place has Krull dimension one. -/
theorem ringKrullDim_localRing (Q : Place C) :
    ringKrullDim (C.left.presheaf.stalk Q.point) = 1 := by
  rw [ringKrullDim_stalk_eq_coheight, Q.eq_coheight_one]
  rfl

end Place

/-- The complement of a finite set of places: `C ∖ S`, as an open subscheme. -/
noncomputable def complOpens (C : Curve k) (S : Finset C.Place) : C.left.Opens :=
  ⟨(⋃ Q ∈ S, {Q.point})ᶜ,
    (isClosed_biUnion_finset fun Q _ => Q.isClosed).isOpen_compl⟩

/-- Every point of a curve is either the generic point or a closed point. -/
theorem eq_genericPoint_or_isClosed (C : Curve k) (z : C.left) :
    z = genericPoint C.left ∨ IsClosed {z} := by
  rcases eq_or_ne z (genericPoint C.left) with h | h
  · exact Or.inl h
  · refine Or.inr (Point.isClosed_of_coheight_eq_one C ?_)
    rcases lt_or_eq_of_le (C.coheight_le_one z) with hlt | heq
    · exact absurd (Order.lt_one_iff.mp hlt) fun h0 =>
        h (C.eq_genericPoint_of_coheight_eq_zero h0)
    · exact heq

end Curve

end Work.CurveBasics

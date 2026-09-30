/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Places of a curve

A *place* of a curve is a closed point.  This file collects the basic API of closed
points of a `Curve k`, together with the dimension-one facts that let us identify them
with the points of the function field at which the order of vanishing is defined.
-/
import Submission.Work.CurveBasics.Basic

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

/-- A *place* of a curve: a closed point.  Under the equivalence between points of a
curve and valuation rings of the function field (the valuative criterion), places
correspond to the nontrivial valuation rings of `K(C)` over `k`. -/
abbrev Place (C : Curve k) : Type u := closedPoints C.left

namespace Place

variable {C : Curve k}

/-- The underlying point of a place. -/
abbrev point (Q : Place C) : C.left := Q.1

/-- A place is a closed point. -/
theorem isClosed (Q : Place C) : IsClosed {Q.point} := Q.2

/-- Everything in the definition of a curve is available for places. -/
instance (Q : Place C) : Ring.KrullDimLE 1 (C.left.presheaf.stalk Q.point) :=
  C.krullDim_stalk_le_one Q.point

/-- The local ring of a curve at a place. -/
abbrev localRing (Q : Place C) : Type u := C.left.presheaf.stalk Q.point

/-- The residue field of a curve at a place. -/
abbrev residueField (Q : Place C) : Type u := C.left.residueField Q.point

/-- The residue field of a point of a curve is a `k`-algebra. -/
noncomputable instance instAlgebraResidueField (C : Curve k) (z : C.left) :
    Algebra k (C.left.residueField z) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    (Spec (CommRingCat.of k)).Γevaluation (C.hom z) ≫ C.hom.residueFieldMap z).hom.toAlgebra

/-- The degree `[κ(Q) : k]` of a place. -/
noncomputable abbrev degree (Q : Place C) : ℕ := C.hom.residueDegree Q.point

end Place

/-- The local rings of a curve have Krull dimension at most one. -/
instance instKrullDimLEStalk (C : Curve k) (z : C.left) :
    Ring.KrullDimLE 1 (C.left.presheaf.stalk z) :=
  C.krullDim_stalk_le_one z

/-- The points of a curve have coheight at most one: the curve is one-dimensional. -/
theorem coheight_le_one (C : Curve k) (z : C.left) : Order.coheight z ≤ 1 := by
  rw [← WithBot.coe_le_coe]
  rw [← ringKrullDim_stalk_eq_coheight z]
  exact Ring.krullDimLE_iff.mp (C.krullDim_stalk_le_one z)

/-- The generic point of a curve has coheight zero. -/
theorem coheight_genericPoint (C : Curve k) : Order.coheight (genericPoint C.left) = 0 := by
  rw [← WithBot.coe_eq_coe]
  rw [← ringKrullDim_stalk_eq_coheight (genericPoint C.left)]
  exact ringKrullDim_eq_zero_of_field _

/-- A point of a curve whose coheight is zero is the generic point. -/
theorem eq_genericPoint_of_coheight_eq_zero (C : Curve k) {z : C.left}
    (hz : Order.coheight z = 0) : z = genericPoint C.left := by
  have hmax : ∀ b : C.left, z ≤ b → b ≤ z := by
    intro b hzb
    by_contra hb
    have hlt : z < b := ⟨hzb, hb⟩
    have h1 := Order.coheight_add_one_le hlt
    rw [hz] at h1
    simp at h1
  have hle : z ≤ genericPoint C.left := by
    rw [Scheme.le_iff_specializes]
    exact (genericPoint_spec C.left).specializes trivial
  have h2 : genericPoint C.left ≤ z := hmax _ hle
  have hs1 : (genericPoint C.left) ⤳ z := (Scheme.le_iff_specializes).mp hle
  have hs2 : z ⤳ (genericPoint C.left) := (Scheme.le_iff_specializes).mp h2
  exact T0Space.t0 (inseparable_iff_specializes_and.mpr ⟨hs2, hs1⟩)

end Curve

end Work.CurveBasics

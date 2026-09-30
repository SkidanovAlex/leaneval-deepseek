/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Points of a base-changed curve (area SpecLin)

An `F`-point `p : Spec F ⟶ C` of a curve `C` over `K` (i.e. a morphism over `Spec K`) induces

* a section `ptLeft p : Spec F ⟶ C_F` of the base-changed curve `C_F = C ×_K Spec F`, and
* a point `ptToPoint p : C_F` of `C_F`, which is *closed* (`ptLeft` is a section of the
  separated morphism `C_F ⟶ Spec F`); the corresponding place is `ptPlace p` and its divisor
  is `ptDiv p`.

The closedness of `ptToPoint p` is proved in `Submission/Work/SpecLin/Points/Closed.lean`.
-/
import Submission.Work.SpecLin.Conventions

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.SpecLin

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {F : Type u} [Field F]
  [Algebra K F]

/-- `R`-valued points of a curve, for an `R`-algebra `R` over the base field. -/
abbrev CurvePt (C : Work.CurveBasics.Curve K) (R : Type u) [CommRing R] [Algebra K R] : Type u :=
  RPt C.toOver R

/-- `F`-valued points of a curve, for a field `F` over the base field. -/
abbrev CurveFPt (C : Work.CurveBasics.Curve K) (F : Type u) [Field F] [Algebra K F] : Type u :=
  RPt C.toOver F

/-- The section `Spec F ⟶ C_F` of the base change determined by an `F`-point of `C`. -/
noncomputable def ptLeft (p : CurveFPt C F) : Spec (CommRingCat.of F) ⟶ (C.baseChange F).left :=
  pullback.lift p.left (𝟙 (Spec (CommRingCat.of F))) (by
    rw [Category.id_comp]
    exact Over.w p)

theorem ptLeft_fst (p : CurveFPt C F) :
    ptLeft p ≫ Work.CurveBasics.Curve.baseChangeFst C F = p.left := by
  change pullback.lift p.left (𝟙 (Spec (CommRingCat.of F))) _ ≫
    pullback.fst C.toOver.hom (Work.CurveBasics.Curve.specMap K F) = p.left
  rw [pullback.lift_fst]

/-- The point of `C_F` determined by an `F`-point of `C`. -/
noncomputable def ptToPoint (p : CurveFPt C F) : (C.baseChange F).left :=
  (ptLeft p).base (IsLocalRing.closedPoint F)

end Work.SpecLin

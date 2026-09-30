/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area CurveFacts
-/
import Submission.Work.Universal.Basic
import Submission.Work.SymQuot.DivBaseInst

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `CurveFacts`: the missing compatibility between `addMap` and the sum morphism

This file records, under its own name, the one piece of data about the symmetric powers that the
chart datum `Work.GroupChunk.Input` does *not* carry, although the additivity of the sum
`Work.Universal.sumDiv` needs it.

`Work.GroupChunk.Input` has
* `addMap m n : Sym^m C ⊗ Sym^n C ⟶ Sym^{m+n} C`, the addition of symmetric powers, and
* `addMap_divOf`, the compatibility of `addMap` with the classification of divisors by points
  (`divOf (lift p q ≫ addMap m n) = divOf p + divOf q`).

What is missing is the compatibility of `addMap` with the *sum morphism*
`sumMap D f k : Sym^k C ⟶ A`: the morphism identity

  `lift p q ≫ addMap m n ≫ sumMap D f (m+n) = (p ≫ sumMap D f m) * (q ≫ sumMap D f n)`,

which is invisible to `divOf` (it is a statement about morphisms into `A`, not about divisors) and
which is *not* derivable from `addMap_divOf` and the quotient property `SymQuotData` alone.  For
the concrete symmetric powers of area `SY` it is however available, in the `powMap` form
`Work.SymQuot.addMap_spec` (`Submission/Work/SymQuot/AddMap.lean`):

  `lift (powMap x) (powMap y) ≫ addMap m n = powMap (Fin.append x y)`.

The predicate `Work.CurveFacts.IsAddSumMap` below is the form of that compatibility needed for
`Work.CurveFacts.kl_add_of_input`, and it is recorded as a hypothesis there.  It is also what makes
`Work.Universal.Input.kl_add` true; that field's statement should therefore be accompanied by this
data (or by a `powMap`-level field of `Work.GroupChunk.Input`).

The same phenomenon occurs in area `KL`, where the compatibility is recorded as explicit data:
`Work.KeyLemma.Curve.SymPow.Add` (the addition morphism) together with
`Work.KeyLemma.Curve.SymPow.IsAddMorphism` (its compatibility with the sum morphisms).
-/
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical MonObj

universe u

namespace Work.CurveFacts

open Work.GCBasics

variable {K : Type u} [Field K]

/-- **The compatibility of the addition of symmetric powers with the sum morphism.**
For a chart datum `D`, a target group object `A` and a morphism `f : C ⟶ A`, this says that the
sum morphism `Σ^{m+n} f` on the sum of two points is the product of `Σ^m f` and `Σ^n f` applied
to the two points.

This is the datum that `Work.GroupChunk.Input` does not carry; it is supplied, for the concrete
symmetric powers, by `Work.SymQuot.addMap_spec` (the `powMap`-level compatibility) together with
`Work.Universal.sumMap_powMap`. -/
def IsAddSumMap {C : Work.CurveBasics.Curve K}
    {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [Work.SpecLin.DivBase C]
    (D : Work.GroupChunk.Input C P0) [Work.Universal.SymQuotData C P0 D]
    {A : Sch K} [GrpObj A] [IsCommMonObj A] (f : C.toOver ⟶ A) (m n : ℕ) : Prop :=
  ∀ {F : Type u} [Field F] [Algebra K F] (p : FPt (D.Sym m) F) (q : FPt (D.Sym n) F),
    (CartesianMonoidalCategory.lift p q ≫ D.addMap m n) ≫ Work.Universal.sumMap D f (m + n) =
      (p ≫ Work.Universal.sumMap D f m) * (q ≫ Work.Universal.sumMap D f n)

/-- The `powMap`-level form of `Work.CurveFacts.IsAddSumMap`: it suffices to check the
compatibility on points of the form `powMap x`.  For the concrete symmetric powers this is
`Work.SymQuot.addMap_spec` together with `Work.Universal.sumMap_powMap`. -/
def IsAddSumMapPow {C : Work.CurveBasics.Curve K}
    {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [Work.SpecLin.DivBase C]
    (D : Work.GroupChunk.Input C P0) [Work.Universal.SymQuotData C P0 D]
    {A : Sch K} [GrpObj A] [IsCommMonObj A] (f : C.toOver ⟶ A) : Prop :=
  ∀ (m n : ℕ) {T : Sch K} (x : Fin m → (T ⟶ C.toOver)) (y : Fin n → (T ⟶ C.toOver)),
    (CartesianMonoidalCategory.lift ((D.symGeom m).powMap x) ((D.symGeom n).powMap y)
        ≫ D.addMap m n) ≫ Work.Universal.sumMap D f (m + n) =
      ((D.symGeom m).powMap x ≫ Work.Universal.sumMap D f m) *
        ((D.symGeom n).powMap y ≫ Work.Universal.sumMap D f n)

end Work.CurveFacts

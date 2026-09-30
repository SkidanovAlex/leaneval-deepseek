/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Points of products, of opens, and of glued schemes (area GB)

This file contains the "glue lemmas" of area GB:

* `FPt.tensorEquiv`: points of a product of `K`-schemes are pairs of points;
* `RPt.factor_of_closed_landsIn`, `FPt.factor_of_landsIn`: a point of `Spec R` (`R` local)
  whose closed point lands in an open subscheme factors through it;
* `Scheme.GlueData.fpt_eq_iff`: two points of the pieces of a gluing agree in the glued
  scheme if and only if they come from a point of the intersection;
* `exists_valuationSubring_dominating`: every point of an integral scheme is dominated by
  a valuation subring of its function field (Mathlib's
  `IsLocalRing.exists_factor_valuationRing`).

The lemma `hom_ext_of_resPt` (two morphisms out of a reduced `K`-scheme agreeing on all
residue-field points are equal) is in `Submission/Work/GCBasics/hom_ext_of_resPt.lean`.
-/
import Submission.Work.GCBasics.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical

universe u

namespace Work.GCBasics

noncomputable section

variable {K : Type u} [Field K]

namespace FPt

/-- Points of a product of `K`-schemes are pairs of points: the universal property of the
product in the category of `K`-schemes, which is the fibre product over `Spec K`. -/
def tensorEquiv (X Y : Sch K) (F : Type u) [Field F] [Algebra K F] :
    FPt (X ⊗ Y) F ≃ FPt X F × FPt Y F :=
  (CartesianMonoidalCategory.liftEquiv).symm

@[simp]
theorem tensorEquiv_apply (X Y : Sch K) (F : Type u) [Field F] [Algebra K F]
    (p : FPt (X ⊗ Y) F) :
    tensorEquiv X Y F p = (p ≫ CategoryTheory.CartesianMonoidalCategory.fst X Y,
      p ≫ CategoryTheory.CartesianMonoidalCategory.snd X Y) := rfl

@[simp]
theorem tensorEquiv_symm_fst (X Y : Sch K) (F : Type u) [Field F] [Algebra K F]
    (p : FPt X F × FPt Y F) :
    (tensorEquiv X Y F).symm p ≫ CategoryTheory.CartesianMonoidalCategory.fst X Y = p.1 := by
  simp [tensorEquiv]

@[simp]
theorem tensorEquiv_symm_snd (X Y : Sch K) (F : Type u) [Field F] [Algebra K F]
    (p : FPt X F × FPt Y F) :
    (tensorEquiv X Y F).symm p ≫ CategoryTheory.CartesianMonoidalCategory.snd X Y = p.2 := by
  simp [tensorEquiv]

@[simp]
theorem tensorEquiv_symm_apply (X Y : Sch K) (F : Type u) [Field F] [Algebra K F]
    (p : FPt X F) (q : FPt Y F) :
    tensorEquiv X Y F ((tensorEquiv X Y F).symm (p, q)) = (p, q) :=
  Equiv.apply_symm_apply _ _

@[simp]
theorem tensorEquiv_apply_symm (X Y : Sch K) (F : Type u) [Field F] [Algebra K F]
    (p : FPt (X ⊗ Y) F) :
    (tensorEquiv X Y F).symm (tensorEquiv X Y F p) = p :=
  Equiv.symm_apply_apply _ _

end FPt

namespace RPt

variable {X : Sch K} {R : Type u} [CommRing R] [Algebra K R] [IsLocalRing R]

/-- A point of `Spec R`, for `R` local, whose closed point lands in an open subscheme `U`
factors through `U`.  Indeed every point of `Spec R` specialises to the closed point, and
an open subscheme is stable under specialisation. -/
theorem factor_of_closed_landsIn (U : X.left.Opens) (p : RPt X R) (h : p.LandsIn U) :
    ∃! q : RPt (Opens.toOver U) R, q ≫ Opens.ιOver U = p := by
  have hmem : ∀ s : Spec (CommRingCat.of R), p.left s ∈ U := fun s =>
    ((IsLocalRing.specializes_closedPoint s).map p.left.continuous).mem_open U.isOpen h
  have hle : Set.range p.left ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨s, rfl⟩
    exact hmem s
  let q0 : Spec (CommRingCat.of R) ⟶ ↑U := IsOpenImmersion.lift U.ι p.left hle
  have hq0 : q0 ≫ U.ι = p.left := IsOpenImmersion.lift_fac U.ι p.left hle
  have hw : q0 ≫ (Opens.toOver U).hom = (specOf K R).hom := by
    change q0 ≫ U.ι ≫ X.hom = (specOf K R).hom
    rw [← Category.assoc, hq0, Over.Hom.w p]
  refine ⟨Over.homMk q0 hw, ?_, ?_⟩
  · dsimp only
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    exact hq0
  · intro q hq
    have hq' : q.left ≫ U.ι = p.left := by
      have h1 := congrArg Over.Hom.left hq
      simpa [Over.comp_left, Opens.ιOver_left] using h1
    apply Over.OverMorphism.ext
    show q.left = q0
    exact IsOpenImmersion.lift_uniq U.ι p.left hle q.left hq'

end RPt

namespace FPt

variable {X : Sch K} {F : Type u} [Field F] [Algebra K F]

/-- A field-valued point whose (unique) point lands in an open subscheme factors through
it.  This is the field case of `RPt.factor_of_closed_landsIn`. -/
theorem factor_of_landsIn (U : X.left.Opens) (p : FPt X F) (h : p.LandsIn U) :
    ∃! q : FPt (Opens.toOver U) F, q ≫ Opens.ιOver U = p :=
  RPt.factor_of_closed_landsIn U p h

end FPt

namespace Scheme.GlueData

variable (D : Scheme.GlueData) {F : Type u} [Field F]

/-- Two points of the pieces `U i` and `U j` of a gluing datum define the same point of the
glued scheme if and only if they are both induced by a point of the intersection
`V (i, j)`.  This is the universal property of `V (i,j)` as the pullback of the two open
immersions into the glued scheme (`Scheme.GlueData.vPullbackConeIsLimit`). -/
theorem fpt_eq_iff (i j : D.J) (p : Spec (CommRingCat.of F) ⟶ D.U i)
    (q : Spec (CommRingCat.of F) ⟶ D.U j) :
    p ≫ D.ι i = q ≫ D.ι j ↔ ∃ r : Spec (CommRingCat.of F) ⟶ D.V (i, j),
      r ≫ D.f i j = p ∧ r ≫ D.t i j ≫ D.f j i = q := by
  constructor
  · intro h
    refine ⟨PullbackCone.IsLimit.lift (D.vPullbackConeIsLimit i j) p q h, ?_, ?_⟩
    · exact PullbackCone.IsLimit.lift_fst (D.vPullbackConeIsLimit i j) p q h
    · exact PullbackCone.IsLimit.lift_snd (D.vPullbackConeIsLimit i j) p q h
  · rintro ⟨r, rfl, rfl⟩
    simp only [Category.assoc, D.glue_condition]

end Scheme.GlueData

/-- `Scheme.GlueData.fpt_eq_iff` under the short name `glueData_fpt_eq_iff`, for callers that
have opened `Work.GCBasics`: a field point of a glued scheme that factors through two pieces
factors through their intersection. -/
theorem glueData_fpt_eq_iff (D : Scheme.GlueData) {F : Type u} [Field F]
    (i j : D.J) (p : Spec (CommRingCat.of F) ⟶ D.U i)
    (q : Spec (CommRingCat.of F) ⟶ D.U j) :
    p ≫ D.ι i = q ≫ D.ι j ↔ ∃ r : Spec (CommRingCat.of F) ⟶ D.V (i, j),
      r ≫ D.f i j = p ∧ r ≫ D.t i j ≫ D.f j i = q :=
  Scheme.GlueData.fpt_eq_iff D i j p q

/-- Every point of an integral scheme is dominated by a valuation subring of its function
field: the image of the local ring `O_{X,x}` in `K(X)` generates a local subring, which is
contained in a valuation subring (`IsLocalRing.exists_factor_valuationRing`). -/
theorem exists_valuationSubring_dominating {X : Scheme.{u}} [IsIntegral X] (x : X) :
    ∃ A : ValuationSubring X.functionField, Dominates A x :=
  IsLocalRing.exists_factor_valuationRing (algebraMap (X.presheaf.stalk x) X.functionField)

end

end Work.GCBasics

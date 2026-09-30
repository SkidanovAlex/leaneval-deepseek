/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area BcDiv: field points of a base change of a `K`-scheme

For fields `K → L → F` and a `K`-scheme `Y`, the `F`-points of the base change
`(Over.pullback (specMap K L)).obj Y` (a scheme over `L`) are the `F`-points of `Y` (a scheme
over `K`): both are "morphisms `Spec F ⟶ Y`" and the `K`-structure on `F` induced by the tower
is the compatible one.  This is the point-level form of the adjunction between `Over.pullback`
and `Over.map`, in the two directions actually used: composition with the projection
`pullback.fst` on one side, and the universal property of the pullback on the other.

## Main definitions

* `Work.BcDiv.pbPtMap` — the projection of a point of the base change;
* `Work.BcDiv.pbPtInv` — a point of `Y` over `K` viewed over the base change;
* `Work.BcDiv.pbPtEquiv` — the resulting equivalence of point sets.

## Main results

* `Work.BcDiv.pbPtEquiv_apply_left` — the projection is composition with `pullback.fst`.
-/
import Submission.Work.BcDiv.Basic
import Submission.Work.SpecLin.Conventions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.BcDiv

noncomputable section

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]
  {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]

/-- The identity comparing the structure morphisms of `Spec F` over `K` and over `L`. -/
theorem specOf_hom_eq (F : Type u) [Field F] [Algebra L F] [Algebra K F]
    [IsScalarTower K L F] :
    (Work.SpecLin.specOf (K := L) F).hom ≫ Curve.specMap K L
      = (Work.SpecLin.specOf (K := K) F).hom := by
  show Spec.map (CommRingCat.ofHom (algebraMap L F))
      ≫ Spec.map (CommRingCat.ofHom (algebraMap K L))
    = Spec.map (CommRingCat.ofHom (algebraMap K F))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq K L F]

/-- **A point of the base change projects to a point of the original scheme.** -/
def pbPtMap (Y : Work.SpecLin.Sch K)
    (p : Work.SpecLin.FPt ((Over.pullback (Curve.specMap K L)).obj Y) F) :
    Work.SpecLin.FPt Y F :=
  Over.homMk (p.left ≫ pullback.fst Y.hom (Curve.specMap K L)) (by
    have hw : p.left ≫ pullback.snd Y.hom (Curve.specMap K L)
        = (Work.SpecLin.specOf (K := L) F).hom := Over.w p
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw, specOf_hom_eq (K := K) (L := L)])

@[simp]
theorem pbPtMap_left (Y : Work.SpecLin.Sch K)
    (p : Work.SpecLin.FPt ((Over.pullback (Curve.specMap K L)).obj Y) F) :
    (pbPtMap Y p).left = p.left ≫ pullback.fst Y.hom (Curve.specMap K L) := rfl

/-- **A point of `Y` over `K` gives a point of the base change**, by the universal property of
the pullback defining the base change. -/
def pbPtInv (Y : Work.SpecLin.Sch K) (q : Work.SpecLin.FPt Y F) :
    Work.SpecLin.FPt ((Over.pullback (Curve.specMap K L)).obj Y) F :=
  Over.homMk
    (pullback.lift q.left (Work.SpecLin.specOf (K := L) F).hom
      ((Over.w q).trans (specOf_hom_eq (K := K) (L := L) F).symm))
    (pullback.lift_snd _ _ _)

/-- The two constructions are inverse to each other. -/
theorem pbPtInv_pbPtMap (Y : Work.SpecLin.Sch K)
    (p : Work.SpecLin.FPt ((Over.pullback (Curve.specMap K L)).obj Y) F) :
    pbPtInv Y (pbPtMap Y p) = p := by
  apply Over.OverMorphism.ext
  show pullback.lift (p.left ≫ pullback.fst Y.hom (Curve.specMap K L))
      (Work.SpecLin.specOf (K := L) F).hom _ = p.left
  refine IsPullback.hom_ext (IsPullback.of_hasPullback Y.hom (Curve.specMap K L)) ?_ ?_
  · rw [pullback.lift_fst]
  · rw [pullback.lift_snd]
    exact (Over.w p).symm

/-- The two constructions are inverse to each other. -/
theorem pbPtMap_pbPtInv (Y : Work.SpecLin.Sch K) (q : Work.SpecLin.FPt Y F) :
    pbPtMap Y (pbPtInv (L := L) Y q) = q := by
  apply Over.OverMorphism.ext
  show (pullback.lift q.left (Work.SpecLin.specOf (K := L) F).hom _)
      ≫ pullback.fst Y.hom (Curve.specMap K L) = q.left
  rw [pullback.lift_fst]

/-- **The `F`-points of the base change to `L` of a `K`-scheme `Y` are the `F`-points of `Y`**,
for a field `F` which is an `L`-algebra and, compatibly, a `K`-algebra. -/
def pbPtEquiv (Y : Work.SpecLin.Sch K) :
    Work.SpecLin.FPt ((Over.pullback (Curve.specMap K L)).obj Y) F ≃ Work.SpecLin.FPt Y F where
  toFun := pbPtMap Y
  invFun := pbPtInv (L := L) Y
  left_inv := pbPtInv_pbPtMap Y
  right_inv := pbPtMap_pbPtInv Y

@[simp]
theorem pbPtEquiv_apply_left (Y : Work.SpecLin.Sch K)
    (p : Work.SpecLin.FPt ((Over.pullback (Curve.specMap K L)).obj Y) F) :
    (pbPtEquiv Y p).left = p.left ≫ pullback.fst Y.hom (Curve.specMap K L) := rfl

end

end Work.BcDiv

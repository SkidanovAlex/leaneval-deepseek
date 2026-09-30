/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area GC — the multiplication of the group chunk `G D`

This file proves `Work.GroupChunk.GroupLaw.mul_exists`: the existence of a morphism
`mul : G D ⊗ G D ⟶ G D` whose class map at every field point is the sum of the class maps of
the two coordinates.

The construction is the gluing of the *pieces* defined in
`Submission/Work/GroupChunk/GroupLaw/MulDefs.lean`: the piece indexed by `a = (i,j,k)` is the
locus in `V ⊗ V` where the RESID map `mulσ i j k` is defined with value in `V`, mapped to
`G D` by that value followed by the `k`-th chart.  Two inputs are used:

* `mulZ_covers_pt` (file `mulZ_covers_pt.lean`): the pieces cover `G D ⊗ G D` at field points;
* `mulCompat` (file `mulCompat.lean`): the pieces agree on the overlaps.

From these, `Scheme.Cover.glueMorphisms` produces the underlying morphism of the
multiplication, and `mulPieceZ_cls` computes its class at field points.
-/
import Mathlib
import Submission.Work.GroupChunk.GroupLaw.MulDefs
import Submission.Work.GroupChunk.GroupLaw.mulZ_covers_pt
import Submission.Work.GroupChunk.GroupLaw.mulCompat

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.GroupChunk.GroupLaw

noncomputable section

open Work.GCBasics
open Work.GroupChunk

variable {K : Type u} [Field K] {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
  [SpecLin.DivBase C]

/-- The `covers` condition of the open cover of `G D ⊗ G D` by the pieces. -/
private theorem mulZ_covers (D : Input C P0) (h : MulCovers D) (x : (GMul D).left) :
    ∃ a : MIdx D, ∃ y : (Opens.toOver (mulZ D a)).left, (mulPieceGG D a).left y = x := by
  obtain ⟨a, v, hv⟩ := h (resPt (GMul D) x)
  refine ⟨a, v.left (IsLocalRing.closedPoint (resField (GMul D) x)), ?_⟩
  have h1 : ((mulPieceGG D a).left) (v.left (IsLocalRing.closedPoint (resField (GMul D) x)))
      = (v ≫ mulPieceGG D a).left (IsLocalRing.closedPoint (resField (GMul D) x)) := rfl
  rw [h1, hv]
  exact resPt_apply (GMul D) x _

/-- The open cover of `G D ⊗ G D` by the pieces. -/
private def mulCover (D : Input C P0) (h : MulCovers D) : (GMul D).left.OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (MIdx D)
    (fun a => (Opens.toOver (mulZ D a)).left)
    (fun a => (mulPieceGG D a).left)
    (fun x => mulZ_covers D h x)

/-- The underlying morphism of the multiplication. -/
private def mulLeft (D : Input C P0) (hcover : MulCovers D) (hcompat : MulCompat D) :
    (GMul D).left ⟶ (GSch D).left :=
  Scheme.Cover.glueMorphisms (mulCover D hcover) (fun a => (mulPieceZ D a).left)
    (fun a b => hcompat a b)

private theorem mulCover_f_glue (D : Input C P0) (hcover : MulCovers D) (hcompat : MulCompat D)
    (a : MIdx D) :
    (mulCover D hcover).f a ≫ mulLeft D hcover hcompat = (mulPieceZ D a).left :=
  Scheme.Cover.ι_glueMorphisms (mulCover D hcover) (fun a => (mulPieceZ D a).left)
    (fun a b => hcompat a b) a

private theorem mulLeft_ι (D : Input C P0) (hcover : MulCovers D) (hcompat : MulCompat D) (a : MIdx D) :
    (mulPieceGG D a).left ≫ mulLeft D hcover hcompat = (mulPieceZ D a).left :=
  mulCover_f_glue D hcover hcompat a

/-- The multiplication `G D ⊗ G D ⟶ G D`. -/
private def mulHom (D : Input C P0) (hcover : MulCovers D) (hcompat : MulCompat D) :
    GMul D ⟶ GSch D :=
  Over.homMk (mulLeft D hcover hcompat) (by
    refine Scheme.Cover.hom_ext (mulCover D hcover) _ _ (fun a => ?_)
    obtain ⟨i, j, k⟩ := a
    rw [← Category.assoc, mulCover_f_glue D hcover hcompat (i, j, k)]
    have hL : (mulPieceZ D (i, j, k)).left ≫ (GSch D).hom
        = (mulZtoW D (i, j, k)).left ≫ (mulW D i j k).ι ≫ (SymSym D).hom := by
      have h1 : (mulPieceZ D (i, j, k)).left
          = (mulZtoW D (i, j, k)).left ≫ (mulPiece D i j k).left := rfl
      rw [h1, Category.assoc, Over.w (mulPiece D i j k)]
      rfl
    have hR : (mulCover D hcover).f (i, j, k) ≫ (GMul D).hom
        = (mulZtoW D (i, j, k)).left ≫ (mulW D i j k).ι ≫ (SymSym D).hom := by
      show (mulPieceGG D (i, j, k)).left ≫ (GMul D).hom
        = (mulZtoW D (i, j, k)).left ≫ (mulW D i j k).ι ≫ (SymSym D).hom
      have h1 : (mulPieceGG D (i, j, k)).left
          = (Opens.ιOver (mulZ D (i, j, k))).left ≫ (chartH D i ⊗ₘ chartH D j).left := rfl
      rw [h1, Category.assoc, Over.w (chartH D i ⊗ₘ chartH D j), ← Over.w (eVV D)]
      rw [← Category.assoc]
      rw [show Over.Hom.left (Opens.ιOver (mulZ D (i, j, k))) ≫ Over.Hom.left (eVV D)
          = Over.Hom.left (mulZtoW D (i, j, k)) ≫ Over.Hom.left (Opens.ιOver (mulW D i j k)) from by
        rw [← Over.comp_left, ← Over.comp_left, mulZtoW_ιOver]]
      rw [Category.assoc]
      rfl
    exact hL.trans hR.symm)

private theorem mulHom_left (D : Input C P0) (hcover : MulCovers D) (hcompat : MulCompat D) :
    (mulHom D hcover hcompat).left = mulLeft D hcover hcompat := rfl

/-- The class of the multiplication at a field point is the sum of the classes of the two
coordinates. -/
private theorem mulHom_cls (D : Input C P0) (hcover : MulCovers D) (hcompat : MulCompat D)
    {F : Type u} [Field F] [Algebra K F] (u : FPt (GMul D) F) :
    D.cls (u ≫ mulHom D hcover hcompat)
      = D.cls (u ≫ fst (GSch D) (GSch D)) + D.cls (u ≫ snd (GSch D) (GSch D)) := by
  obtain ⟨a, v, hv⟩ := hcover u
  have h1 : u ≫ mulHom D hcover hcompat = v ≫ mulPieceZ D a := by
    apply Over.OverMorphism.ext
    show u.left ≫ mulLeft D hcover hcompat = v.left ≫ (mulPieceZ D a).left
    rw [← congrArg Over.Hom.left hv, Over.comp_left, Category.assoc,
      mulLeft_ι D hcover hcompat a]
  rw [h1, mulPieceZ_cls D a v]
  congr 1
  · rw [← hv, Category.assoc]
  · rw [← hv, Category.assoc]

/-- The auxiliary form of the main theorem: from the cover and the compatibility of the pieces
we obtain the multiplication. -/
private theorem mul_exists_aux (D : Input C P0) (hcover : MulCovers D) (hcompat : MulCompat D) :
    ∃ mul : GMul D ⟶ GSch D,
      ∀ {F : Type u} [Field F] [Algebra K F] (p q : FPt (GSch D) F),
        D.cls (CartesianMonoidalCategory.liftEquiv (p, q) ≫ mul) = D.cls p + D.cls q := by
  refine ⟨mulHom D hcover hcompat, ?_⟩
  intro F hF hAlg p q
  rw [mulHom_cls D hcover hcompat (CartesianMonoidalCategory.liftEquiv (p, q)),
    CartesianMonoidalCategory.liftEquiv_apply, CartesianMonoidalCategory.lift_fst,
    CartesianMonoidalCategory.lift_snd]

/-- **The multiplication of the group chunk.**  There is a morphism `G D ⊗ G D ⟶ G D` whose
class map at every field point is the sum of the class maps of the two coordinates. -/
theorem mul_exists {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
    [Work.SpecLin.DivBase C] (D : Work.GroupChunk.Input C P0)
    [IsSeparated (Work.GroupChunk.GSch D).hom]
    [GeometricallyReduced (Work.GroupChunk.GSch D).hom] :
    ∃ mul : MonoidalCategoryStruct.tensorObj (Work.GroupChunk.GSch D)
        (Work.GroupChunk.GSch D) ⟶ Work.GroupChunk.GSch D,
      ∀ {F : Type u} [Field F] [Algebra K F]
        (p q : Work.GCBasics.FPt (Work.GroupChunk.GSch D) F),
        Work.GroupChunk.Input.cls D
            (CartesianMonoidalCategory.liftEquiv (p, q) ≫ mul) =
          Work.GroupChunk.Input.cls D p + Work.GroupChunk.Input.cls D q := by
  exact mul_exists_aux D (mulZ_covers_pt D)
    (mulCompat D ‹IsSeparated (Work.GroupChunk.GSch D).hom›)

end

end Work.GroupChunk.GroupLaw

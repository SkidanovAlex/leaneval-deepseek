import Mathlib
import Submission.Work.GroupChunk.GroupLaw.MulDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area GC — the compatibility of the pieces of the multiplication

The multiplication of the group chunk `G D` is glued from the piece maps
`mulPieceZ D a : mulZ D a ⟶ G D` into the group chunk, which are defined on the piece opens
`mulZ D a ⊆ V ⊗ V`.  For the gluing to descend to a morphism `G D ⊗ G D ⟶ G D` the pieces have
to agree on their overlaps; this is the statement `MulCompat D`.

The proof is the standard one for maps into the glued group chunk: two morphisms into `G D` out
of a reduced `K`-scheme are equal as soon as their classes agree at every residue-field point
(`Work.GroupChunk.Input.hom_ext_cls`).  On the overlap of the pieces `a` and `b` both composites
map a point to a point of `G D ⊗ G D` — and these two points agree because the overlap *is* the
pullback of the two piece inclusions — so their classes, computed by `mulPieceZ_cls` as the sum
of the classes of the two coordinates, agree.
-/
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

/-! ## The overlap of two pieces -/

/-- The overlap of the pieces `a` and `b` of the multiplication, as a `K`-scheme: the
pullback of the two piece inclusions into `G D ⊗ G D`, with the structure morphism induced by
the first piece. -/
abbrev mulPb (D : Input C P0) (a b : MIdx D) : Sch K :=
  Over.mk (pullback.fst (mulPieceGG D a).left (mulPieceGG D b).left
    ≫ (Opens.toOver (mulZ D a)).hom)

/-- The first projection of the overlap, as a morphism of `K`-schemes. -/
def mulPbFst (D : Input C P0) (a b : MIdx D) : mulPb D a b ⟶ Opens.toOver (mulZ D a) :=
  Over.homMk (pullback.fst (mulPieceGG D a).left (mulPieceGG D b).left) rfl

/-- The second projection of the overlap, as a morphism of `K`-schemes. -/
def mulPbSnd (D : Input C P0) (a b : MIdx D) : mulPb D a b ⟶ Opens.toOver (mulZ D b) :=
  Over.homMk (pullback.snd (mulPieceGG D a).left (mulPieceGG D b).left) (by
    show pullback.snd (mulPieceGG D a).left (mulPieceGG D b).left
        ≫ (Opens.toOver (mulZ D b)).hom
      = pullback.fst (mulPieceGG D a).left (mulPieceGG D b).left
        ≫ (Opens.toOver (mulZ D a)).hom
    calc pullback.snd (mulPieceGG D a).left (mulPieceGG D b).left
          ≫ (Opens.toOver (mulZ D b)).hom
        = pullback.snd (mulPieceGG D a).left (mulPieceGG D b).left
            ≫ ((mulPieceGG D b).left ≫ (GMul D).hom) := by rw [← Over.w (mulPieceGG D b)]
      _ = (pullback.snd (mulPieceGG D a).left (mulPieceGG D b).left
            ≫ (mulPieceGG D b).left) ≫ (GMul D).hom := by rw [Category.assoc]
      _ = (pullback.fst (mulPieceGG D a).left (mulPieceGG D b).left
            ≫ (mulPieceGG D a).left) ≫ (GMul D).hom := by rw [← pullback.condition]
      _ = pullback.fst (mulPieceGG D a).left (mulPieceGG D b).left
            ≫ ((mulPieceGG D a).left ≫ (GMul D).hom) := by rw [Category.assoc]
      _ = pullback.fst (mulPieceGG D a).left (mulPieceGG D b).left
            ≫ (Opens.toOver (mulZ D a)).hom := by rw [Over.w (mulPieceGG D a)])

theorem mulPbFst_left (D : Input C P0) (a b : MIdx D) :
    (mulPbFst D a b).left = pullback.fst (mulPieceGG D a).left (mulPieceGG D b).left := rfl

theorem mulPbSnd_left (D : Input C P0) (a b : MIdx D) :
    (mulPbSnd D a b).left = pullback.snd (mulPieceGG D a).left (mulPieceGG D b).left := rfl

/-- The overlap of two pieces is reduced: it is an open subscheme of the reduced piece `a`. -/
instance instIsReducedMulPb (D : Input C P0) (a b : MIdx D) : IsReduced (mulPb D a b).left :=
  isReduced_of_isOpenImmersion (pullback.snd (mulPieceGG D a).left (mulPieceGG D b).left)

/-! ## The compatibility -/

/-- **The pieces agree on the overlaps**, at the level of `K`-schemes. -/
theorem mulPbZ_compat (D : Input C P0) (a b : MIdx D) [IsSeparated (GSch D).hom] :
    mulPbFst D a b ≫ mulPieceZ D a = mulPbSnd D a b ≫ mulPieceZ D b := by
  apply hom_ext_of_resPt (K := K)
  intro y
  refine D.cls_injective (D := D) ?_
  rw [← Category.assoc, ← Category.assoc]
  rw [mulPieceZ_cls D a (resPt (mulPb D a b) y ≫ mulPbFst D a b),
      mulPieceZ_cls D b (resPt (mulPb D a b) y ≫ mulPbSnd D a b)]
  have hQ : (resPt (mulPb D a b) y ≫ mulPbFst D a b) ≫ mulPieceGG D a
      = (resPt (mulPb D a b) y ≫ mulPbSnd D a b) ≫ mulPieceGG D b := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, mulPbFst_left, mulPbSnd_left, Category.assoc]
    exact congrArg (fun w => (resPt (mulPb D a b) y).left ≫ w) pullback.condition
  have hfst := congrArg (fun w => D.cls (w ≫ fst (GSch D) (GSch D))) hQ
  have hsnd := congrArg (fun w => D.cls (w ≫ snd (GSch D) (GSch D))) hQ
  simp only [Category.assoc] at hfst hsnd ⊢
  rw [hfst, hsnd]

/-- **The compatibility of the pieces on the overlaps**, i.e. the descent condition for
gluing the piece maps into a morphism `G D ⊗ G D ⟶ G D`. -/
theorem mulCompat {K : Type*} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : CategoryTheory.MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
    [Work.SpecLin.DivBase C] (D : Work.GroupChunk.Input C P0)
    (hsep : Work.GroupChunk.GroupLaw.GSep D) :
    Work.GroupChunk.GroupLaw.MulCompat D := by
  intro a b
  haveI : IsSeparated (GSch D).hom := hsep
  exact congrArg Over.Hom.left (mulPbZ_compat D a b)

end

end Work.GroupChunk.GroupLaw

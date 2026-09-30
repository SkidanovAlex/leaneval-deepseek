import Mathlib
import Submission.Work.SymQuot.RelQuot.Setup
import Submission.Work.SymQuot.RelQuot.Defs
import Submission.Work.SymQuot.RelQuot.PieceMaps
import Submission.Work.SymQuot.RelQuot.Cover
import Submission.Work.SymQuot.RelQuot.pieceCover_mem
import Submission.Work.SymQuot.RelQuot.pieceCoverXY_mem
import Submission.Work.SymQuot.RelQuot.pieceMap_isOpenImmersion
import Submission.Work.SymQuot.RelQuot.pieceCoverQY_locallyDirected
import Submission.Work.SymQuot.RelQuot.relativeQuotAffinePiece
import Submission.Work.SymQuot.Invariants.tensor_fixedPoints
import Submission.Work.SymQuot.Invariants.tensor_fixedPoints_of_flat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.unusedVariables false

namespace Work.SymQuot.RelQuot

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped MonoidalCategory Classical

open CategoryTheory Limits AlgebraicGeometry in
open scoped MonoidalCategory in
theorem relQuot {K : Type u} [Field K] (X Y Z : Work.SpecLin.Sch K) {Γ : Type u} [Group Γ]
    [Fintype Γ] [IsSeparated X.hom] [IsSeparated Y.hom]
    (D : QuotientData Γ X.left) (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom)
    (f : X ⊗ Y ⟶ Z) (hf : ∀ g : Γ, (actOver X D hbase g ▷ Y) ≫ f = f) :
    ∃! h : relQuotScheme X D hbase ⊗ Y ⟶ Z, (relQuotSchemeMap X D hbase ▷ Y) ≫ h = f := by
  classical
  obtain ⟨ld, hld_trans⟩ := pieceCoverQY_locallyDirected (X := X) (Y := Y) D hbase
  letI : Preorder (pieceCoverQY (X := X) (Y := Y) D hbase).I₀ := instPreorderPieceCoverQY D hbase
  letI : Category (pieceCoverQY (X := X) (Y := Y) D hbase).I₀ := instCategoryPieceCoverQY D hbase
  letI : (pieceCoverQY (X := X) (Y := Y) D hbase).LocallyDirected := ld
  -- the piece maps
  have piece : ∀ i : pieceIdx D Y,
      ∃! g : (chartU D hbase i.1 ⊗ ovV i.2) ⟶ Z,
        (chartMapOv D hbase i.1 ▷ ovV i.2) ≫ g = (ovIncl (D := D) i.1 ⊗ₘ ovVι i.2) ≫ f :=
    fun i => relativeQuotAffinePiece D hbase i.1 i.2
      ((ovIncl (D := D) i.1 ⊗ₘ ovVι i.2) ≫ f)
      (fun g => actU_tensor_invariant D hbase i.1 i.2 f hf g)
  let g : ∀ i : pieceIdx D Y, (chartU D hbase i.1 ⊗ ovV i.2) ⟶ Z := fun i => (piece i).choose
  have g_spec : ∀ i : pieceIdx D Y, (chartMapOv D hbase i.1 ▷ ovV i.2) ≫ g i
      = (ovIncl (D := D) i.1 ⊗ₘ ovVι i.2) ≫ f := fun i => (piece i).choose_spec.1
  have g_uniq : ∀ (i : pieceIdx D Y) (g' : (chartU D hbase i.1 ⊗ ovV i.2) ⟶ Z),
      (chartMapOv D hbase i.1 ▷ ovV i.2) ≫ g' = (ovIncl (D := D) i.1 ⊗ₘ ovVι i.2) ≫ f →
      g' = g i := fun i => (piece i).choose_spec.2
  -- compatibility of the piece maps with the transition maps
  have hcompatOv : ∀ {i j : pieceIdx D Y} (hij : i ⟶ j),
      pieceTrans D hbase (leOfHom hij).1 (leOfHom hij).2 ≫ g j = g i := by
    intro i j hij
    refine g_uniq i _ ?_
    rw [← Category.assoc, chartMapOv_pieceTrans D hbase (leOfHom hij).1 (leOfHom hij).2,
      Category.assoc, g_spec j, ← Category.assoc,
      ovUMap_tensor_ovVMap D (leOfHom hij).1 (leOfHom hij).2]
  have hcompat : ∀ {i j : pieceIdx D Y} (hij : i ⟶ j),
      (pieceCoverQY (X := X) (Y := Y) D hbase).trans hij ≫ (g j).left = (g i).left := by
    intro i j hij
    rw [show (pieceCoverQY (X := X) (Y := Y) D hbase).trans hij
        = (pieceTrans D hbase (leOfHom hij).1 (leOfHom hij).2).left from hld_trans hij,
      ← Over.comp_left _ _ _ (pieceTrans D hbase (leOfHom hij).1 (leOfHom hij).2) (g j),
      hcompatOv hij]
  have hw : ∀ i : pieceIdx D Y, (g i).left ≫ Z.hom
      = (pieceCoverQY (X := X) (Y := Y) D hbase).f i
        ≫ (relQuotScheme X D hbase ⊗ Y).hom := by
    intro i
    rw [pieceCoverQY_f_eq, (g i).w]
    exact ((chartιOv D hbase i.1 ⊗ₘ ovVι i.2).w).symm
  -- glue
  let h : (relQuotScheme X D hbase ⊗ Y) ⟶ Z :=
    (pieceCoverQY (X := X) (Y := Y) D hbase).glueMorphismsOverOfLocallyDirected
      (fun i => (g i).left) hcompat hw
  have hh : ∀ i : pieceIdx D Y,
      (pieceCoverQY (X := X) (Y := Y) D hbase).f i ≫ h.left = (g i).left :=
    fun i => (pieceCoverQY (X := X) (Y := Y) D hbase).map_glueMorphismsOverOfLocallyDirected_left
      (fun i => (g i).left) hcompat hw i
  -- the triangle
  have hfac : (relQuotSchemeMap X D hbase ▷ Y) ≫ h = f := by
    apply Over.OverMorphism.ext
    refine (pieceCoverXY (X := X) (Y := Y) D).hom_ext _ _ (fun i => ?_)
    show (pieceCoverXY (X := X) (Y := Y) D).f i
        ≫ ((relQuotSchemeMap X D hbase ▷ Y) ≫ h).left
      = (pieceCoverXY (X := X) (Y := Y) D).f i ≫ f.left
    rw [pieceCoverXY_f_eq]
    conv_lhs => rw [Over.comp_left _ _ _ _ _, ← Category.assoc, ← Over.comp_left _ _ _ _ _,
      ovIncl_tensor_quot D hbase i.1 i.2, Over.comp_left _ _ _ _ _, Category.assoc,
      ← pieceCoverQY_f_eq, hh i, ← Over.comp_left _ _ _ _ _, g_spec i, Over.comp_left _ _ _ _ _]
  -- uniqueness
  have hchar : ∀ (i : pieceIdx D Y) (h'' : (relQuotScheme X D hbase ⊗ Y) ⟶ Z),
      (relQuotSchemeMap X D hbase ▷ Y) ≫ h'' = f →
      (chartιOv D hbase i.1 ⊗ₘ ovVι i.2).left ≫ h''.left = (g i).left := by
    intro i h'' hh''
    have key : (chartMapOv D hbase i.1 ▷ ovV i.2) ≫
        ((chartιOv D hbase i.1 ⊗ₘ ovVι i.2) ≫ h'')
        = (ovIncl (D := D) i.1 ⊗ₘ ovVι i.2) ≫ f := by
      rw [← Category.assoc, ← ovIncl_tensor_quot D hbase i.1 i.2, Category.assoc, hh'']
    rw [← Over.comp_left _ _ _ (chartιOv D hbase i.1 ⊗ₘ ovVι i.2) h'']
    exact congrArg Over.Hom.left (g_uniq i _ key)
  refine ⟨h, hfac, fun h' hh' => ?_⟩
  apply Over.OverMorphism.ext
  refine (pieceCoverQY (X := X) (Y := Y) D hbase).hom_ext _ _ (fun i => ?_)
  show (pieceCoverQY (X := X) (Y := Y) D hbase).f i ≫ h'.left
    = (pieceCoverQY (X := X) (Y := Y) D hbase).f i ≫ h.left
  rw [hh i, pieceCoverQY_f_eq]
  exact hchar i h' hh'

end Work.SymQuot.RelQuot

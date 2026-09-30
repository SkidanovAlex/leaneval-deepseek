/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The piece cover of `(X/Γ) ⊗ Y` (area SY, `relQuot`)

For a quotient datum `D` of an action of a finite group `Γ` on a `K`-scheme `X` and a `K`-scheme
`Y`, the relative quotient `(X/Γ) ⊗ Y` is covered by the *pieces* `(chart U) ⊗ V`, where `U` runs
through the invariant affine charts of `X` and `V` through the affine opens of `Y`; the piece of
`X ⊗ Y` is `U ⊗ V`.  This file provides

* `Work.SymQuot.RelQuot.pieceCoverQY` — the open cover of `(relQuotScheme X D hbase) ⊗ Y` by the
  pieces `chartU D hbase U ⊗ ovV V`;
* `Work.SymQuot.RelQuot.pieceCoverXY` — the open cover of `X ⊗ Y` by the pieces
  `ovU U ⊗ ovV V`;
* the open immersion statements for the piece maps (`isOpenImmersion_ovIncl_tensor`,
  `isOpenImmersion_pieceTrans`).
-/
import Mathlib
import Submission.Work.SymQuot.RelQuot.PieceMaps
import Submission.Work.SymQuot.RelQuot.pieceCover_mem
import Submission.Work.SymQuot.RelQuot.pieceMap_isOpenImmersion
import Submission.Work.SymQuot.RelQuot.pieceCoverXY_mem

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Work.SymQuot.RelQuot

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct Classical MonoidalCategory

variable {K : Type u} [Field K] {Γ : Type u} [Group Γ] [Fintype Γ] {X Y : Work.SpecLin.Sch K}


/-- The index type of the piece cover: charts of `D` and affine opens of `Y`. -/
abbrev pieceIdx (D : QuotientData Γ X.left) (Y : Work.SpecLin.Sch K) :=
  D.Chart × Y.left.affineOpens

noncomputable instance instPreorderPieceIdx (D : QuotientData Γ X.left) (Y : Work.SpecLin.Sch K) :
    Preorder (pieceIdx D Y) := inferInstance

noncomputable instance instCategoryPieceIdx (D : QuotientData Γ X.left) (Y : Work.SpecLin.Sch K) :
    Category (pieceIdx D Y) := Preorder.smallCategory _

/-- **The piece `ovU U ⊗ ovV V ⟶ X ⊗ Y` is an open immersion.** -/
theorem isOpenImmersion_ovIncl_tensor (D : QuotientData Γ X.left) (U : D.Chart)
    (V : Y.left.affineOpens) :
    IsOpenImmersion (ovIncl (D := D) U ⊗ₘ ovVι V).left := by
  rw [Over.tensorHom_left]
  simp only [ovIncl_left, ovVι_left]
  exact Scheme.pullback_map_isOpenImmersion _ _ _ _ (U.1.ι) (V.1.ι)
    (𝟙 (Spec (CommRingCat.of K)))
    (by rw [Category.comp_id, ovU_hom]) (by rw [Category.comp_id, ovV_hom])

/-- **The transition map of the piece cover is an open immersion.** -/
theorem isOpenImmersion_pieceTrans (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) {U U' : D.Chart} {V V' : Y.left.affineOpens}
    (h : U ≤ U') (h' : V ≤ V') : IsOpenImmersion (pieceTrans D hbase h h').left := by
  rw [pieceTrans, Over.tensorHom_left]
  simp only [chartResOv_left, ovVMap_left]
  haveI := Work.SymQuot.Chart.chartRes_isOpenImmersion_alt D.action h U'.2.1 U.2.1 U'.2.2 U.2.2
  exact Scheme.pullback_map_isOpenImmersion _ _ _ _ (D.action.chartRes U.1 U'.1 h U'.2.2 U.2.2)
    (Scheme.homOfLE Y.left h') (𝟙 (Spec (CommRingCat.of K)))
    (by rw [Category.comp_id]; exact (Over.w (chartResOv D hbase h)).symm)
    (by rw [Category.comp_id]; exact (Over.w (ovVMap (Y := Y) h')).symm)

/-- **The cover of `(X/Γ) ⊗ Y` by the pieces `(chart U) ⊗ V`.** -/
noncomputable abbrev pieceCoverQY (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) :
    ((relQuotScheme X D hbase) ⊗ Y).left.OpenCover where
  I₀ := pieceIdx D Y
  X i := (chartU D hbase i.1 ⊗ ovV i.2).left
  f i := (chartιOv D hbase i.1 ⊗ₘ ovVι i.2).left
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun i => pieceMap_isOpenImmersion D hbase i.1 i.2⟩
    obtain ⟨U, V, hx⟩ := pieceCover_mem D hbase x
    exact ⟨(U, V), hx⟩

noncomputable instance instPreorderPieceCoverQY (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) :
    Preorder (pieceCoverQY (X := X) (Y := Y) D hbase).I₀ :=
  inferInstanceAs (Preorder (pieceIdx D Y))

noncomputable instance instCategoryPieceCoverQY (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) :
    Category (pieceCoverQY (X := X) (Y := Y) D hbase).I₀ :=
  Preorder.smallCategory _

/-- The piece map of the cover of `(X/Γ) ⊗ Y`, as an `Over` morphism. -/
lemma pieceCoverQY_f_eq (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom)
    (i : D.Chart × Y.left.affineOpens) :
    (pieceCoverQY (X := X) (Y := Y) D hbase).f i
      = (chartιOv D hbase i.1 ⊗ₘ ovVι i.2).left := rfl

/-- **The cover of `X ⊗ Y` by the pieces `U ⊗ V`.** -/
noncomputable abbrev pieceCoverXY (D : QuotientData Γ X.left) : (X ⊗ Y).left.OpenCover where
  I₀ := pieceIdx D Y
  X i := (ovU (D := D) i.1 ⊗ ovV i.2).left
  f i := (ovIncl (D := D) i.1 ⊗ₘ ovVι i.2).left
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun i => isOpenImmersion_ovIncl_tensor D i.1 i.2⟩
    obtain ⟨U, V, hx⟩ := pieceCoverXY_mem D x
    exact ⟨(U, V), hx⟩

noncomputable instance instPreorderPieceCoverXY (D : QuotientData Γ X.left) :
    Preorder (pieceCoverXY (X := X) (Y := Y) D).I₀ :=
  inferInstanceAs (Preorder (pieceIdx D Y))

noncomputable instance instCategoryPieceCoverXY (D : QuotientData Γ X.left) :
    Category (pieceCoverXY (X := X) (Y := Y) D).I₀ :=
  Preorder.smallCategory _

/-- The piece map of the cover of `X ⊗ Y`. -/
lemma pieceCoverXY_f_eq (D : QuotientData Γ X.left) (i : pieceIdx D Y) :
    (pieceCoverXY (X := X) (Y := Y) D).f i = (ovIncl (D := D) i.1 ⊗ₘ ovVι i.2).left := rfl

/-- The piece of the cover of `X ⊗ Y`. -/
lemma pieceCoverXY_X_eq (D : QuotientData Γ X.left) (i : pieceIdx D Y) :
    (pieceCoverXY (X := X) (Y := Y) D).X i = (ovU (D := D) i.1 ⊗ ovV i.2).left := rfl

/-- The piece of the cover of `(X/Γ) ⊗ Y`. -/
lemma pieceCoverQY_X_eq (D : QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom) (i : pieceIdx D Y) :
    (pieceCoverQY (X := X) (Y := Y) D hbase).X i
      = (chartU D hbase i.1 ⊗ ovV i.2).left := rfl

end Work.SymQuot.RelQuot

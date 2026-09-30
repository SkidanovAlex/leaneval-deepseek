/-
# The stage quotient map is the local map of the new cell

For a `PolyCW` `P`, a cell `a` and a stage `T` of `a`, the map induced by the
subdivision on the pieces of the stage step (`PolyCW.stageQuotMap`) is the local
map of the cell `a`, up to the identifications of the two pieces with the local
models `unitCx (P.dim a)` and `locCx P a`:

`(cellPieceS).quot ≅ unitCx (P.dim a)`  and  `(sdPieceS).quot ≅ locCx P a`.

This is the support-form analogue of `PolyCW.cellPiece_quotMap_eq_locMap`
(`Work.Subdivision.PieceSquare`) and it is the input to the cell-by-cell
induction over the localized filtration (`StageInduction.lean`): combined with
the local condition `LocallySpherical P hdd haug` it makes the stage step a
quasi-isomorphism.
-/
import Mathlib
import Submission.Work.MbarHomology.Local.SupportPieces
import Submission.Work.MbarHomology.Local.cellPieceSCoeffF_bijective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory

universe u

namespace Work.Subdivision

namespace PolyCW

variable (P : PolyCW.{u})

set_option allowUnsafeReducibility true
attribute [local reducible] cellChain sdChain cellS sdS cellSMod sdSMod leSub ltSub
  SubData.chain SubData.quot SubData.quotOf PolyCW.icF PolyCW.ioF

/-! ### The cellular piece of a stage step is the model complex -/

/-- The model complex `unitCx d` is trivial away from degree `d`. -/
theorem unitCx_subsingleton' (d : ℕ) {k : ℕ} (hk : k ≠ d) :
    Subsingleton ((unitCx.{u} d).X k) :=
  ModuleCat.subsingleton_of_isZero
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) d unitMod.{u} k hk)

theorem cellPieceSMap_isIso (hdd : P.HasDdZero) {T : Finset P.Cell} (a : P.Cell)
    (h : IsStage P a T) : IsIso (cellPieceSMap P hdd a h) := by
  have coeff : IsIso (cellPieceSCoeffF P hdd a h) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact Work.MbarHomology.Local.cellPieceSCoeffF_bijective P hdd a h
  haveI hf : ∀ k, IsIso ((cellPieceSMap P hdd a h).f k) := fun k => by
    by_cases hk : k = P.dim a
    · subst hk
      rw [cellPieceSMap_f_self]
      infer_instance
    · rw [ConcreteCategory.isIso_iff_bijective]
      haveI : Subsingleton ((unitCx (P.dim a)).X k) := unitCx_subsingleton' (P.dim a) hk
      haveI : Subsingleton ((cellPieceS P hdd a h).quot.X k) :=
        cellPieceS_subsingleton P hdd a h hk
      refine ⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components (cellPieceSMap P hdd a h)

/-- **The cellular piece of a stage step is the one-dimensional model complex.** -/
noncomputable def cellPieceSIso (hdd : P.HasDdZero) {T : Finset P.Cell} (a : P.Cell)
    (h : IsStage P a T) : (cellPieceS P hdd a h).quot ≅ unitCx (P.dim a) := by
  haveI := cellPieceSMap_isIso P hdd a h
  exact (asIso (cellPieceSMap P hdd a h)).symm

@[simp] theorem cellPieceSIso_inv (hdd : P.HasDdZero) {T : Finset P.Cell} (a : P.Cell)
    (h : IsStage P a T) :
    (cellPieceSIso P hdd a h).inv = cellPieceSMap P hdd a h := rfl

end PolyCW

end Work.Subdivision

namespace Work.MbarHomology.Local

/-! ### The main statement -/

theorem stageQuotMap_eq_locMap (P : Work.Subdivision.PolyCW) (hdd : P.HasDdZero) (haug : P.HasAugZero) {T : Finset P.Cell} (a : P.Cell) (h : Work.Subdivision.PolyCW.IsStage P a T) : ∃ (Φ : CategoryTheory.Iso (Work.Subdivision.SubData.quot (Work.Subdivision.PolyCW.cellPieceS P hdd a h)) (Work.Subdivision.unitCx (P.dim a))) (Ψ : CategoryTheory.Iso (Work.Subdivision.SubData.quot (Work.Subdivision.PolyCW.sdPieceS P a h)) (Work.Subdivision.PolyCW.locCx P a)), CategoryTheory.CategoryStruct.comp (Work.Subdivision.PolyCW.stageQuotMap P hdd haug a h) Ψ.hom = CategoryTheory.CategoryStruct.comp Φ.hom (Work.Subdivision.PolyCW.locMap P hdd haug a) := by
  haveI hcell : IsIso (Work.Subdivision.PolyCW.cellPieceSMap P hdd a h) :=
    Work.Subdivision.PolyCW.cellPieceSMap_isIso P hdd a h
  refine ⟨(asIso (Work.Subdivision.PolyCW.cellPieceSMap P hdd a h)).symm,
    Work.Subdivision.PolyCW.sdPieceSIso P h, ?_⟩
  show CategoryTheory.CategoryStruct.comp (Work.Subdivision.PolyCW.stageQuotMap P hdd haug a h)
      (Work.Subdivision.PolyCW.sdPieceSIso P h).hom =
    CategoryTheory.CategoryStruct.comp (asIso (Work.Subdivision.PolyCW.cellPieceSMap P hdd a h)).inv
      (Work.Subdivision.PolyCW.locMap P hdd haug a)
  have h2 : (Work.Subdivision.PolyCW.stageQuotMap P hdd haug a h) =
      (asIso (Work.Subdivision.PolyCW.cellPieceSMap P hdd a h)).inv ≫
        (Work.Subdivision.PolyCW.locMap P hdd haug a) ≫
        (Work.Subdivision.PolyCW.sdPieceSMap P h) := by
    have hid : (asIso (Work.Subdivision.PolyCW.cellPieceSMap P hdd a h)).inv ≫
        (Work.Subdivision.PolyCW.cellPieceSMap P hdd a h) = 𝟙 _ :=
      Iso.inv_hom_id (asIso (Work.Subdivision.PolyCW.cellPieceSMap P hdd a h))
    rw [← Work.Subdivision.PolyCW.cellPieceSMap_stageQuotMap P hdd haug a h,
      ← Category.assoc, hid, Category.id_comp]
  rw [h2]
  rw [← Work.Subdivision.PolyCW.sdPieceSIso_inv P h]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id, Category.comp_id]

end Work.MbarHomology.Local

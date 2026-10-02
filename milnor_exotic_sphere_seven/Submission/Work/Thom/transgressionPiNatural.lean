import Mathlib
import Submission.Work.Thom.tsqHonest
import Submission.Work.Thom.transgressionPiAux
import Submission.Work.Cohomology.relCohMV_honest_les
import Submission.Work.Thom.transgressionNatural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.Thom

/-- The pullback of the absolute cohomology of the base to the total space (`TsqH.piTop`) is the
pullback along the projection on honest relative cohomology. -/
theorem piTop_eq_relPb {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι) (j : ℕ) :
    Work.Thom.TsqH.piTop Z j
      = Work.Thom.relPb (Work.Thom.bundleProj Z) j := by
  rw [Work.Thom.TsqH.piTop]
  have h := Work.Thom.relCohMap_relToAbs (Work.Thom.bundleProj Z) (∅ : Set Z.TotalSpace)
    (∅ : Set B) (fun _ h => h) ℤ j
  rw [show (Work.Thom.pdCohIso B j).hom = Work.Thom.relToAbs ℤ (∅ : Set B) j from rfl]
  rw [← CategoryTheory.Category.assoc, ← h, CategoryTheory.Category.assoc]
  rw [show (Work.Thom.relToAbs ℤ (∅ : Set Z.TotalSpace) j)
    = (Work.Thom.pdCohIso Z.TotalSpace j).hom from rfl]
  simp only [CategoryTheory.Iso.hom_inv_id, CategoryTheory.Category.comp_id]

/-- The pullback of the absolute cohomology of the overlap to the total space
(`TsqH.piOv`) is the pullback along the restriction of the projection to the overlap, on honest
relative cohomology. -/
theorem piOv_eq_relCohMap {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι) {U V : Set B}
    (k : ℕ) :
    Work.Thom.TsqH.piOv Z U V k
      = Work.Thom.relCohMap (Work.Thom.fPieceProj (Work.Thom.bundleProj Z) U V)
          (∅ : Set ↥(Z.proj ⁻¹' U ∩ Z.proj ⁻¹' V)) (∅ : Set ↥(U ∩ V))
          (fun _ h => h) ℤ k := by
  rw [Work.Thom.TsqH.piOv]
  have h := Work.Thom.relCohMap_relToAbs (Work.Thom.pieceProj Z (U ∩ V))
    (∅ : Set ↥(Z.proj ⁻¹' (U ∩ V))) (∅ : Set ↥(U ∩ V)) (fun _ h => h) ℤ k
  rw [show (Work.Thom.pdCohIso ↥(U ∩ V) k).hom
    = Work.Thom.relToAbs ℤ (∅ : Set ↥(U ∩ V)) k from rfl]
  rw [← CategoryTheory.Category.assoc, ← h, CategoryTheory.Category.assoc]
  rw [show (Work.Thom.relToAbs ℤ (∅ : Set ↥(Z.proj ⁻¹' (U ∩ V))) k)
    = (Work.Thom.pdCohIso ↥(Z.proj ⁻¹' (U ∩ V)) k).hom from rfl]
  rw [show (Work.Thom.pdCohIso ↥(Z.proj ⁻¹' (U ∩ V)) k)
    = (Work.Thom.pdCohIso ↥(Z.proj ⁻¹' U ∩ Z.proj ⁻¹' V) k) from by congr 1]
  simp only [CategoryTheory.Iso.hom_inv_id, CategoryTheory.Category.comp_id]
  rfl

theorem transgressionPiNatural (B : Type) [TopologicalSpace B] (F : Type) [NormedAddCommGroup F]
    [NormedSpace ℝ F] (ι : Type) (Z : Work.TangentClasses.RealBundle B F ι) {U V : Set B}
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ) :
    (CategoryTheory.CategoryStruct.comp
        (Work.Cohomology.honestDelta (TopCat.of B) (∅ : Set B) U V hU hV hcov k)
        (Work.Thom.TsqH.piTop Z (k + 1)))
      = (CategoryTheory.CategoryStruct.comp
          (Work.Thom.TsqH.piOv Z U V k)
          (Work.Cohomology.honestDelta (TopCat.of Z.TotalSpace) (∅ : Set Z.TotalSpace)
            (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) (hU.preimage Z.continuous_proj)
            (hV.preimage Z.continuous_proj) (Work.Thom.preimage_union_univ Z hcov) k)) := by
  rw [piTop_eq_relPb Z (k + 1),
    piOv_eq_relCohMap (Z := Z) (U := U) (V := V) k]
  exact Work.Thom.transgressionNatural (Work.Thom.bundleProj Z) hU hV hcov k

end Work.Thom

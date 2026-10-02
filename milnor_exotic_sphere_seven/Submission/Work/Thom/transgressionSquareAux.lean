import Mathlib
import Submission.Work.Thom.TransgressionSquare
import Submission.Work.Thom.Glue
import Submission.Work.Thom.tsqHonest
import Submission.Work.Thom.transgressionSameSpace
import Submission.Work.Thom.transgressionPiNatural
import Submission.Work.Cohomology.relCohMV_honest_les

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The transgression square of the Mayer--Vietoris ladder

This file proves `Work.Thom.TransgressionSquare`: the compatibility of the Thom map
`x ↦ π^*(x) ⌣ τ` with the Mayer--Vietoris connecting maps of the base and of the Thom pair.

The proof is assembled from two clean statements, proved in the sibling modules
`Submission/Work/Thom/transgressionSameSpace.lean` and
`Submission/Work/Thom/transgressionPiNatural.lean`:

* `Work.Thom.transgressionSameSpace` — for a single space `X`, a pair `(X,A)` and a cover
  `U ∪ V = X`, cupping with a relative class `b ∈ H^n(X,A)` intertwines the connecting map of
  the absolute Mayer--Vietoris sequence of `(X,∅)` with that of the relative one of `(X,A)`;
* `Work.Thom.transgressionPiNatural` — naturality of the absolute Mayer--Vietoris connecting map
  of the base under the projection `π : E → B` of a real bundle.

The remaining content of this file is bookkeeping: the identification of the two `T`-maps of the
statements with `Work.Thom.thomMap` and `Work.Thom.localThomMap` (`Work.Thom.TsqH.Ttop`,
`Work.Thom.TsqH.Tov`), and the comparison isomorphisms `Work.Thom.pdCohIso`.
-/

open Work.TangentClasses

namespace Work.Thom

open CategoryTheory
open Work.Cohomology

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## The comparison isomorphisms -/

/-- The absolutely-relative comparison `pdCohIso` is compatible with the pullback along the
projection `π : E → B` and with `TsqH.piTop`. -/
theorem piTop_iso (Z : RealBundle B F ι) (j : ℕ) :
    TsqH.piTop Z j ≫ (pdCohIso Z.TotalSpace j).hom
      = (pdCohIso B j).hom ≫ CohMap (bundleProj Z) ℤ j := by
  unfold TsqH.piTop
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The elementwise form of `piTop_iso`. -/
theorem piTop_apply (Z : RealBundle B F ι) (j : ℕ)
    (z : pdCoh (TopCat.of B) (∅ : Set B) j) :
    (pdCohIso Z.TotalSpace j).hom ((TsqH.piTop Z j).hom z)
      = (CohMap (bundleProj Z) ℤ j).hom ((pdCohIso B j).hom z) := by
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (piTop_iso Z j)) z
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- The comparison `pdCohIso` is compatible with the pullback of the piece over the overlap and
with `TsqH.piOv`. -/
theorem piOv_iso (Z : RealBundle B F ι) (U V : Set B) (k : ℕ) :
    TsqH.piOv Z U V k ≫ (pdCohIso ↥(Z.proj ⁻¹' U ∩ Z.proj ⁻¹' V) k).hom
      = (pdCohIso ↥(U ∩ V) k).hom ≫ CohMap (pieceProj Z (U ∩ V)) ℤ k := by
  unfold TsqH.piOv
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The elementwise form of `piOv_iso`. -/
theorem piOv_apply (Z : RealBundle B F ι) (U V : Set B) (k : ℕ)
    (z : pdCohSub (TopCat.of B) (∅ : Set B) (U ∩ V) k) :
    (pdCohIso ↥(Z.proj ⁻¹' U ∩ Z.proj ⁻¹' V) k).hom ((TsqH.piOv Z U V k).hom z)
      = (CohMap (pieceProj Z (U ∩ V)) ℤ k).hom ((pdCohIso ↥(U ∩ V) k).hom z) := by
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (piOv_iso Z U V k)) z
  exact h

/-- The restriction of a relative class of the Thom pair to the overlap of the pulled-back cover
is the restriction `PieceRes` to the piece over `U ∩ V`. -/
theorem relRestrOvl_pieceRes (Z : RealBundle B F ι) (U V : Set B) (n : ℕ)
    (τ : OpenThom Z n) :
    TsqH.relRestrOvl (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n τ = PieceRes Z (U ∩ V) n τ := rfl

/-! ## The two comparison maps on elements -/

/-- The top comparison map `TsqH.Ttop` is the mixed cup product with `b`. -/
theorem Ttop_apply (X : TopCat) (A : Set X) (n j : ℕ) (b : RelCoh ℤ n X A)
    (z : pdCoh X (∅ : Set X) j) :
    (TsqH.Ttop X A n b j).hom z
      = (mixedCupC ℤ A j n) ((pdCohIso X j).hom z) b := rfl

/-- The overlap comparison map `TsqH.Tov` is the mixed cup product with the restricted class. -/
theorem Tov_apply (X : TopCat) (A U V : Set X) (n k : ℕ) (b : RelCoh ℤ n X A)
    (z : pdCohSub X (∅ : Set X) (U ∩ V) k) :
    (TsqH.Tov X A U V n b k).hom z
      = (mixedCupC ℤ (interAU A (U ∩ V)) k n)
          ((pdCohIso ↥(U ∩ V) k).hom z) ((TsqH.relRestrOvl X A U V n).hom b) := rfl

/-! ## The transgression square -/

/-- **The transgression square**: for every real bundle `Z → B`, every `n` and every class
`τ ∈ H^n(E,E∖0)`, the Thom map is compatible with the Mayer--Vietoris connecting maps of the base
and of the Thom pair. -/
theorem transgressionSquareAux (B : Type) [TopologicalSpace B] (F : Type) [NormedAddCommGroup F]
    [NormedSpace ℝ F] (ι : Type) (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ) {U V : Set B}
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (τ : Work.Thom.OpenThom Z n) :
    Work.Thom.TransgressionSquare Z n hU hV hcov τ := by
  intro k y
  set hU' : IsOpen (Z.proj ⁻¹' U) := hU.preimage Z.continuous_proj with hU'def
  set hV' : IsOpen (Z.proj ⁻¹' V) := hV.preimage Z.continuous_proj with hV'def
  set hc' : Z.proj ⁻¹' U ∪ Z.proj ⁻¹' V = Set.univ := preimage_union_univ Z hcov with hc'def
  set ŷ : pdCohSub (TopCat.of B) (∅ : Set B) (U ∩ V) k :=
    (pdCohIso ↥(U ∩ V) k).symm.hom y with hŷ
  have hŷ' : (pdCohIso ↥(U ∩ V) k).hom ŷ = y := by
    rw [hŷ]; exact Iso.inv_hom_id_apply _ y
  have hT : (thomMap Z n τ (k + 1))
        ((pdCohIso B (k + 1)).hom
          ((honestDelta (TopCat.of B) (∅ : Set B) U V hU hV hcov k).hom ŷ))
      = (TsqH.Ttop (TopCat.of Z.TotalSpace) (zeroComplement Z) n τ (k + 1)).hom
          ((TsqH.piTop Z (k + 1)).hom
            ((honestDelta (TopCat.of B) (∅ : Set B) U V hU hV hcov k).hom ŷ)) := by
    rw [thomMap_apply, Ttop_apply]
    rw [piTop_apply Z (k + 1)
      ((honestDelta (TopCat.of B) (∅ : Set B) U V hU hV hcov k).hom ŷ)]
  have hpi : (TsqH.piTop Z (k + 1)).hom
        ((honestDelta (TopCat.of B) (∅ : Set B) U V hU hV hcov k).hom ŷ)
      = (honestDelta (TopCat.of Z.TotalSpace) (∅ : Set Z.TotalSpace)
            (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) hU' hV' hc' k).hom
          ((TsqH.piOv Z U V k).hom ŷ) := by
    have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (transgressionPiNatural B F ι Z hU hV hcov k)) ŷ
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  have key : (TsqH.Ttop (TopCat.of Z.TotalSpace) (zeroComplement Z) n τ (k + 1)).hom
        ((honestDelta (TopCat.of Z.TotalSpace) (∅ : Set Z.TotalSpace)
            (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) hU' hV' hc' k).hom
          ((TsqH.piOv Z U V k).hom ŷ))
      = (eqToHom (congrArg (fun m => pdCoh (TopCat.of Z.TotalSpace) (zeroComplement Z) m)
            (by omega : k + n + 1 = (k + 1) + n))).hom
        ((honestDelta (TopCat.of Z.TotalSpace) (zeroComplement Z)
            (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) hU' hV' hc' (k + n)).hom
          ((TsqH.Tov (TopCat.of Z.TotalSpace) (zeroComplement Z)
            (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n τ k).hom ((TsqH.piOv Z U V k).hom ŷ))) := by
    have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (transgressionSameSpace (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) hU' hV' hc' n τ k)) ((TsqH.piOv Z U V k).hom ŷ)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h
  have h4 : (TsqH.Tov (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n τ k).hom ((TsqH.piOv Z U V k).hom ŷ)
      = (localThomMap Z n (U ∩ V) (PieceRes Z (U ∩ V) n τ) k) y := by
    rw [Tov_apply]
    unfold localThomMap
    simp only [LinearMap.comp_apply]
    rw [show (TsqH.relRestrOvl (TopCat.of Z.TotalSpace) (zeroComplement Z)
          (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n).hom τ
        = (PieceRes Z (U ∩ V) n).hom τ from by rw [relRestrOvl_pieceRes]]
    rw [piOv_apply, hŷ']
    rfl
  rw [hT, hpi, key, h4]

end

end Work.Thom

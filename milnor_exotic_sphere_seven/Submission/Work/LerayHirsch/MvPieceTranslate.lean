import Mathlib
import Submission.Work.LerayHirsch.LhTwoCoverDefs
import Submission.Work.LerayHirsch.lhMap_comap
import Submission.Work.LerayHirsch.MvPieceIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [-instance] AddCommGroup.toIntModule

/-!
# The comparison maps of the two-cover Mayer--Vietoris ladder, on the pieces

`Submission/Work/LerayHirsch/LhTwoCoverDefs.lean` builds, over the cover `U ∪ V = B`, the
comparison maps `MvTU`, `MvTV`, `MvTQ` from the base ladder to the ladder of `P(E)`.  This module
identifies them with the Leray--Hirsch maps of the restricted bundles: under the canonical
identification `pieceMap : P(Z|_W) ≅ π⁻¹W` and the absolute--relative comparison `pdCohIso`,

  `MvTU Z W k = lhAny (Z|_W) k`  (and similarly `MvTV = MvTU V`, `MvTQ = MvTU (U ∩ V)`).

Consequently `MvTU Z W k` is an isomorphism whenever `LerayHirschFull (Z|_W)` holds.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom Work.Cohomology
open CategoryTheory CategoryTheory.Limits

noncomputable section
variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-! ## The piece cup map in the absolute cohomology of the piece -/

/-- The piece cup map, read in the absolute cohomology of the piece. -/
theorem pdCohIso_luCupMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (π : C(Y, X)) (n : ℕ) {U : Set X}
    (cU : pdCohSub (TopCat.of Y) (∅ : Set Y) (π ⁻¹' U) n) (k : ℕ)
    (z : Coh ℤ k ↥U) :
    (pdCohIso ↥(π ⁻¹' U) (k + n)).hom (luCupMap π (∅ : Set Y) n cU k z)
      = cupH' ℤ (Work.Whitney.ssB ↥(π ⁻¹' U)) k n
          ((CohMap (luFPiece π U) ℤ k).hom z)
          ((pdCohIso ↥(π ⁻¹' U) n).hom cU) :=
  mixedCup_relToAbs (X := ↥(π ⁻¹' U))
    (interAU (X := TopCat.of Y) (∅ : Set Y) (π ⁻¹' U)) k n
    ((CohMap (luFPiece π U) ℤ k).hom z) cU

/-- Pullback naturality of the cup product. -/
theorem CohMap_cupH'_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n mm : ℕ) (x : Coh ℤ n Y) (y : Coh ℤ mm Y) :
    (CohMap f ℤ (n + mm)).hom (cupH' ℤ (Work.Whitney.ssB Y) n mm x y)
      = cupH' ℤ (Work.Whitney.ssB X) n mm
          ((CohMap f ℤ n).hom x) ((CohMap f ℤ mm).hom y) :=
  Work.Cohomology.cupNaturalH ℤ (TopCat.ofHom f) n mm x y

/-- The degree transport is insensitive to the proof. -/
theorem cohTransport_eq_cohTransportLM {B : Type} [TopologicalSpace B] {n n' : ℕ}
    (h h' : n = n') (x : Coh ℤ n B) : cohTransport h x = cohTransportLM h' x := by
  rw [Work.Thom.cohTransportLM_apply, Subsingleton.elim h h']

/-! ## The identification of the piece with `P(Z|_W)` -/

/-- `luFPiece` of the projection of `P(Z)`, composed with `pieceMap`, is the projection of
`P(Z|_W)`. -/
theorem luFPiece_projMap_comp_pieceMap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (W : Set B) :
    (luFPiece (projMap Z) W).comp (pieceMap Z W)
      = projMap (bundleComap Z (subtypeMap W)) := by
  ext x
  exact projMap_projMapComap Z (subtypeMap W) x

/-- Pushing a class in degree `k` through the projection of the piece. -/
theorem CohMap_pieceMap_luFPiece (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (W : Set B) (k : ℕ) (z : Coh ℤ k ↥W) :
    (CohMap (pieceMap Z W) ℤ k).hom ((CohMap (luFPiece (projMap Z) W) ℤ k).hom z)
      = (CohMap (projMap (bundleComap Z (subtypeMap W))) ℤ k).hom z := by
  rw [Work.Thom.CohMap_comp_apply (pieceMap Z W) (luFPiece (projMap Z) W) ℤ k z,
    luFPiece_projMap_comp_pieceMap]

/-- The tautological class restricted to the piece pulls back to the tautological class of the
restricted bundle. -/
theorem CohMap_pieceMap_zetaRelPiece (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    [Fintype ι] (W : Set B) (i : ℕ) :
    (CohMap (pieceMap Z W) ℤ (2 * i)).hom
        ((pdCohIso ↥(projMap Z ⁻¹' W) (2 * i)).hom (zetaRelPiece Z W i))
      = zetaPow (bundleComap Z (subtypeMap W)) i := by
  have h2 : (pdCohIso ↥(projMap Z ⁻¹' W) (2*i)).hom
        ((pdCohRes (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' W) (2*i)).hom
          (zetaRel Z i))
      = (CohMap (subtypeMap (projMap Z ⁻¹' W)) ℤ (2*i)).hom
          ((pdCohIso (ProjSpace Z) (2*i)).hom (zetaRel Z i)) := by
    have h1 := congrArg (fun (φ : pdCoh (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (2*i) ⟶
        Coh ℤ (2*i) ↥(projMap Z ⁻¹' W)) => (ModuleCat.Hom.hom φ) (zetaRel Z i))
      (pdCohRes_pdCohIso (ProjSpace Z) (projMap Z ⁻¹' W) (2*i))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, restrCoh] at h1
    exact h1
  rw [zetaRelPiece_def, h2]
  rw [show (pdCohIso (ProjSpace Z) (2*i)).hom (zetaRel Z i) = zetaPow Z i from
    Iso.inv_hom_id_apply (pdCohIso (ProjSpace Z) (2*i)) (zetaPow Z i)]
  rw [Work.Thom.CohMap_comp_apply (pieceMap Z W) (subtypeMap (projMap Z ⁻¹' W)) ℤ (2*i)
    (zetaPow Z i)]
  rw [show (subtypeMap (projMap Z ⁻¹' W)).comp (pieceMap Z W)
      = projMapComap Z (subtypeMap W) from by ext x; rfl]
  exact zetaPow_comap Z (subtypeMap W) i

/-! ## The individual summands -/

/-- **The `i`-th summand of the comparison map on the piece**, in the `Coh` model. -/
theorem MvCU_translate (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (W : Set B) (k : ℕ) (i : lhIdx m k)
    (a : ↑(pdCohSub (TopCat.of B) (∅ : Set B) W (k - 2 * (i : ℕ)))) :
    (CohMap (pieceMap Z W) ℤ k).hom
        ((pdCohIso ↥(projMap Z ⁻¹' W) k).hom ((MvCU Z W k i).hom a))
      = cohTransportLM (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k)
          (cupH' ℤ (Work.Whitney.ssB (ProjSpace (bundleComap Z (subtypeMap W))))
              (k - 2 * (i : ℕ)) (2 * (i : ℕ))
            ((CohMap (projMap (bundleComap Z (subtypeMap W))) ℤ (k - 2 * (i : ℕ))).hom
              ((pdCohIso ↥W (k - 2 * (i : ℕ))).hom a))
            (zetaPow (bundleComap Z (subtypeMap W)) i)) := by
  rw [show (MvCU Z W k i).hom a
      = (pdSubCast (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z)) (projMap Z ⁻¹' W)
          (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k)).hom
        (luCupMap (projMap Z) (∅ : Set (ProjSpace Z)) (2 * (i : ℕ)) (zetaRelPiece Z W i)
          (k - 2 * (i : ℕ)) ((pdCohIso ↥W (k - 2 * (i : ℕ))).hom a)) from rfl]
  refine Eq.trans (congrArg (fun w => (CohMap (pieceMap Z W) ℤ k).hom w)
    (pdCohIso_pdSubCast (TopCat.of (ProjSpace Z)) (projMap Z ⁻¹' W)
      (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k) _)) ?_
  rw [Work.Whitney.cohTransport_CohMap]
  rw [pdCohIso_luCupMap]
  rw [CohMap_cupH'_apply]
  rw [CohMap_pieceMap_luFPiece, CohMap_pieceMap_zetaRelPiece]
  exact cohTransport_eq_cohTransportLM _ _ _

/-! ## The comparison maps -/

/-- **The comparison map `MvTU` on the piece is the Leray--Hirsch map of the restricted
bundle.** -/
theorem MvTU_translate (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (W : Set B) (k : ℕ) (x : ↑(MvW B m k W)) :
    (CohMap (pieceMap Z W) ℤ k).hom
        ((pdCohIso ↥(projMap Z ⁻¹' W) k).hom ((MvTU Z W k).hom x))
      = lhAny (bundleComap Z (subtypeMap W)) k
          (fun i => (pdCohIso ↥W (k - 2 * (i : ℕ))).hom (x i)) := by
  rw [MvTU_apply]
  rw [show (pdCohIso ↥(projMap Z ⁻¹' W) k).hom (∑ i : lhIdx m k, (MvCU Z W k i).hom (x i))
      = ∑ i : lhIdx m k, (pdCohIso ↥(projMap Z ⁻¹' W) k).hom ((MvCU Z W k i).hom (x i))
      from map_sum _ _ Finset.univ]
  rw [show (CohMap (pieceMap Z W) ℤ k).hom
        (∑ i : lhIdx m k, (pdCohIso ↥(projMap Z ⁻¹' W) k).hom ((MvCU Z W k i).hom (x i)))
      = ∑ i : lhIdx m k, (CohMap (pieceMap Z W) ℤ k).hom
          ((pdCohIso ↥(projMap Z ⁻¹' W) k).hom ((MvCU Z W k i).hom (x i)))
      from map_sum _ _ Finset.univ]
  rw [lhAny, lhAnyLM, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MvCU_translate Z W k i (x i), lhAnySummand]
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, evalLM]
  congr 1

/-- **The comparison map `MvTV` on the piece is the Leray--Hirsch map of the restricted
bundle.** -/
theorem MvTV_translate (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (V : Set B) (k : ℕ) (x : ↑(MvW B m k V)) :
    (CohMap (pieceMap Z V) ℤ k).hom
        ((pdCohIso ↥(projMap Z ⁻¹' V) k).hom ((MvTV Z V k).hom x))
      = lhAny (bundleComap Z (subtypeMap V)) k
          (fun i => (pdCohIso ↥V (k - 2 * (i : ℕ))).hom (x i)) :=
  MvTU_translate Z V k x

/-- **The comparison map `MvTQ` on the overlap is the Leray--Hirsch map of the restricted
bundle.** -/
theorem MvTQ_translate (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U V : Set B) (k : ℕ) (x : ↑(MvQ B m k U V)) :
    (CohMap (pieceMap Z (U ∩ V)) ℤ k).hom
        ((pdCohIso ↥(projMap Z ⁻¹' (U ∩ V)) k).hom
          ((MvOvlIso Z U V k).hom ((MvTQ Z U V k).hom x)))
      = lhAny (bundleComap Z (subtypeMap (U ∩ V))) k
          (fun i => (pdCohIso ↥(U ∩ V) (k - 2 * (i : ℕ))).hom (x i)) := by
  rw [show (MvOvlIso Z U V k).hom
      = 𝟙 (pdCohSub (TopCat.of (ProjSpace Z)) (∅ : Set (ProjSpace Z))
          (projMap Z ⁻¹' U ∩ projMap Z ⁻¹' V) k) from rfl]
  simp only [ModuleCat.hom_id, LinearMap.id_apply]
  exact MvTU_translate Z (U ∩ V) k x

/-! ## The comparison maps are isomorphisms on the pieces -/

/-- **`MvTU` is an isomorphism when the restricted bundle satisfies Leray--Hirsch.** -/
theorem isIso_MvTU (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (W : Set B) (hW : ∀ k : ℕ, Function.Bijective (lhAny (bundleComap Z (subtypeMap W)) k))
    (k : ℕ) : CategoryTheory.IsIso (MvTU Z W k) := by
  haveI := isIso_CohMap_pieceMap Z W k
  have hbi : Function.Bijective (CohMap (pieceMap Z W) ℤ k).hom :=
    CategoryTheory.ConcreteCategory.bijective_of_isIso (CohMap (pieceMap Z W) ℤ k)
  have hpd : Function.Injective (pdCohIso ↥(projMap Z ⁻¹' W) k).hom :=
    (CategoryTheory.ConcreteCategory.bijective_of_isIso
      (pdCohIso ↥(projMap Z ⁻¹' W) k).hom).1
  have hinj : Function.Injective (MvTU Z W k).hom := by
    intro x y hxy
    have h1 : lhAny (bundleComap Z (subtypeMap W)) k
        (fun i => (pdCohIso ↥W (k - 2 * (i : ℕ))).hom (x i))
        = lhAny (bundleComap Z (subtypeMap W)) k
          (fun i => (pdCohIso ↥W (k - 2 * (i : ℕ))).hom (y i)) := by
      rw [← MvTU_translate Z W k x, ← MvTU_translate Z W k y, hxy]
    have h2 := (hW k).1 h1
    funext i
    exact (CategoryTheory.ConcreteCategory.bijective_of_isIso
      (pdCohIso ↥W (k - 2 * (i : ℕ))).hom).1 (congrFun h2 i)
  have hsurj : Function.Surjective (MvTU Z W k).hom := by
    intro z
    obtain ⟨v, hv⟩ := (hW k).2
      ((CohMap (pieceMap Z W) ℤ k).hom ((pdCohIso ↥(projMap Z ⁻¹' W) k).hom z))
    let x : ↑(MvW B m k W) := fun i : lhIdx m k => (pdCohIso ↥W (k - 2 * (i : ℕ))).inv (v i)
    refine ⟨x, ?_⟩
    apply hpd
    apply hbi.1
    rw [MvTU_translate Z W k x]
    have hxv : (fun i : lhIdx m k => (pdCohIso ↥W (k - 2 * (i : ℕ))).hom (x i)) = v := by
      funext i
      exact Iso.inv_hom_id_apply (pdCohIso ↥W (k - 2 * (i : ℕ))) (v i)
    rw [hxv, hv]
  rw [isIso_iff_mono_and_epi, ModuleCat.mono_iff_injective, ModuleCat.epi_iff_surjective]
  exact ⟨hinj, hsurj⟩

/-- **`MvTV` is an isomorphism when the restricted bundle satisfies Leray--Hirsch.** -/
theorem isIso_MvTV (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (V : Set B) (hV : ∀ k : ℕ, Function.Bijective (lhAny (bundleComap Z (subtypeMap V)) k))
    (k : ℕ) : CategoryTheory.IsIso (MvTV Z V k) :=
  isIso_MvTU Z V hV k

/-- **`MvTQ` is an isomorphism when the restricted bundle satisfies Leray--Hirsch.** -/
theorem isIso_MvTQ (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (U V : Set B)
    (hUV : ∀ k : ℕ, Function.Bijective (lhAny (bundleComap Z (subtypeMap (U ∩ V))) k))
    (k : ℕ) : CategoryTheory.IsIso (MvTQ Z U V k) :=
  isIso_MvTU Z (U ∩ V) hUV k

end
end Work.LerayHirsch

import Mathlib
import Submission.Work.ANALYTIC.CechPt.CoordDefs
import Submission.Work.ANALYTIC.CechPt.kMap_solidEquiv
import Submission.Work.ANALYTIC.CechPt.doubleDualUnit_sigma_unit
import Submission.Work.ANALYTIC.CechPt.ddZf_iso_prod
import Submission.Work.ANALYTIC.ihom_sigma_unit_iso
import Submission.Work.ANALYTIC.solidEquiv_biprod
import Submission.Work.ANALYTIC.solidDual_iso_zfree_of_finite

set_option backward.isDefEq.respectTransparency false

namespace Work.ANALYTIC.CechPt

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

noncomputable section

/-! ## The reduced Haar coordinate map -/

/-- **The coordinates of `kMap`.**  The `j`-th coordinate of the Haar coordinate map `kMap T`,
composed with the projection `qred` onto the reduced object, is the dual element `lamJ T j`. -/
theorem qred_kMap_π (T : LightProfinite.{0}) [Infinite T] (j : ℕ) :
    Work.ATOM.qred T (Work.ATOM.levelData T).s₀ ≫
        (kMap T ≫ CategoryTheory.Limits.Pi.π (fun _ : ℕ => 𝟙_ LightCondAb) j) =
      lamJ T j := by
  have hπ : Work.ANALYTIC.prodZisoProdLCZ.inv ≫
        CategoryTheory.Limits.Pi.π (fun _ : ℕ => 𝟙_ LightCondAb) j =
      CategoryTheory.Limits.Pi.π (fun _ : ℕ => Work.ATOM.ZS.Unred.LCZ) j ≫
        Work.ANALYTIC.ZisoLCZ.inv :=
    CategoryTheory.Limits.Pi.mapIso_inv_π (fun _ : ℕ => Work.ANALYTIC.ZisoLCZ) j
  have h1 : kMap T ≫ CategoryTheory.Limits.Pi.π (fun _ : ℕ => 𝟙_ LightCondAb) j =
      Work.ANALYTIC.kappaTilde T j ≫ Work.ANALYTIC.ZisoLCZ.inv := by
    rw [kMap, Category.assoc, hπ, ← Category.assoc, Work.ANALYTIC.kLCZ,
      CategoryTheory.Limits.Pi.lift_comp_π]
  rw [h1, ← Category.assoc, Work.ANALYTIC.kappaTilde_spec, lamJ]

/-! ## The splitting `ℤ[T] ≅ ℤ[pt] ⊞ ℤ̃[T]`, with explicit components -/

/-- The splitting map `ℤ[T] ⟶ ℤ[pt] ⊞ ℤ̃[T]`: the augmentation together with the projection
onto the reduced object. -/
noncomputable def splitMap (T : LightProfinite.{0}) [Infinite T] :
    zf T ⟶ zf Work.ATOM.pt ⊞ Work.ATOM.zred T (Work.ATOM.levelData T).s₀ :=
  CategoryTheory.Limits.biprod.lift (Work.ATOM.aug T)
    (Work.ATOM.qred T (Work.ATOM.levelData T).s₀)

theorem splitMap_fst (T : LightProfinite.{0}) [Infinite T] :
    splitMap T ≫ CategoryTheory.Limits.biprod.fst = Work.ATOM.aug T :=
  CategoryTheory.Limits.biprod.lift_fst _ _

theorem splitMap_snd (T : LightProfinite.{0}) [Infinite T] :
    splitMap T ≫ CategoryTheory.Limits.biprod.snd =
      Work.ATOM.qred T (Work.ATOM.levelData T).s₀ :=
  CategoryTheory.Limits.biprod.lift_snd _ _

/-- The section of `qred` complementary to `zmap (ptAt s₀)`: the map with
`qred ≫ splitSec = 𝟙 - aug ≫ zmap (ptAt s₀)`. -/
noncomputable def splitSec (T : LightProfinite.{0}) [Infinite T] :
    Work.ATOM.zred T (Work.ATOM.levelData T).s₀ ⟶ zf T :=
  cokernel.desc (Work.ATOM.zmap (Work.ATOM.ptAt (Work.ATOM.levelData T).s₀))
    (𝟙 (zf T) - Work.ATOM.aug T ≫ Work.ATOM.zmap (Work.ATOM.ptAt (Work.ATOM.levelData T).s₀))
    (by
      rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
        Work.ATOM.zmap_ptAt_comp_aug, Category.id_comp, sub_self])

theorem qred_splitSec (T : LightProfinite.{0}) [Infinite T] :
    Work.ATOM.qred T (Work.ATOM.levelData T).s₀ ≫ splitSec T =
      𝟙 (zf T) - Work.ATOM.aug T ≫ Work.ATOM.zmap (Work.ATOM.ptAt (Work.ATOM.levelData T).s₀) :=
  cokernel.π_desc _ _ _

theorem zmap_ptAt_qred (T : LightProfinite.{0}) [Infinite T] :
    Work.ATOM.zmap (Work.ATOM.ptAt (Work.ATOM.levelData T).s₀) ≫
      Work.ATOM.qred T (Work.ATOM.levelData T).s₀ = 0 :=
  cokernel.condition _

theorem splitSec_qred (T : LightProfinite.{0}) [Infinite T] :
    splitSec T ≫ Work.ATOM.qred T (Work.ATOM.levelData T).s₀ =
      𝟙 (Work.ATOM.zred T (Work.ATOM.levelData T).s₀) := by
  apply (cancel_epi (Work.ATOM.qred T (Work.ATOM.levelData T).s₀)).mp
  rw [← Category.assoc, qred_splitSec, Preadditive.sub_comp, Category.id_comp, Category.assoc,
    zmap_ptAt_qred, comp_zero, sub_zero, Category.comp_id]

theorem splitSec_aug (T : LightProfinite.{0}) [Infinite T] :
    splitSec T ≫ Work.ATOM.aug T = 0 := by
  apply (cancel_epi (Work.ATOM.qred T (Work.ATOM.levelData T).s₀)).mp
  rw [← Category.assoc, qred_splitSec, Preadditive.sub_comp, Category.id_comp, Category.assoc,
    Work.ATOM.zmap_ptAt_comp_aug, Category.comp_id, sub_self, comp_zero]

/-- The inverse of the splitting map. -/
noncomputable def splitInv (T : LightProfinite.{0}) [Infinite T] :
    zf Work.ATOM.pt ⊞ Work.ATOM.zred T (Work.ATOM.levelData T).s₀ ⟶ zf T :=
  CategoryTheory.Limits.biprod.desc (Work.ATOM.zmap (Work.ATOM.ptAt (Work.ATOM.levelData T).s₀))
    (splitSec T)

theorem splitMap_comp_splitInv (T : LightProfinite.{0}) [Infinite T] :
    splitMap T ≫ splitInv T = 𝟙 (zf T) := by
  rw [splitMap, splitInv, CategoryTheory.Limits.biprod.lift_desc]
  rw [qred_splitSec]
  abel

theorem splitInv_comp_splitMap (T : LightProfinite.{0}) [Infinite T] :
    splitInv T ≫ splitMap T =
      𝟙 (zf Work.ATOM.pt ⊞ Work.ATOM.zred T (Work.ATOM.levelData T).s₀) := by
  apply CategoryTheory.Limits.biprod.hom_ext'
  · apply CategoryTheory.Limits.biprod.hom_ext
    · calc (biprod.inl ≫ (splitInv T ≫ splitMap T)) ≫ biprod.fst
          = biprod.inl ≫ ((splitInv T ≫ splitMap T) ≫ biprod.fst) :=
              Category.assoc _ _ _
        _ = biprod.inl ≫ (splitInv T ≫ (splitMap T ≫ biprod.fst)) := by rw [Category.assoc]
        _ = biprod.inl ≫ (splitInv T ≫ Work.ATOM.aug T) := by rw [splitMap_fst]
        _ = (biprod.inl ≫ splitInv T) ≫ Work.ATOM.aug T := (Category.assoc _ _ _).symm
        _ = Work.ATOM.zmap (Work.ATOM.ptAt (Work.ATOM.levelData T).s₀) ≫ Work.ATOM.aug T := by
              rw [splitInv, CategoryTheory.Limits.biprod.inl_desc]
        _ = 𝟙 (zf Work.ATOM.pt) := Work.ATOM.zmap_ptAt_comp_aug T _
        _ = biprod.inl ≫ biprod.fst := (CategoryTheory.Limits.biprod.inl_fst).symm
        _ = (biprod.inl ≫ 𝟙 (zf Work.ATOM.pt ⊞ Work.ATOM.zred T (Work.ATOM.levelData T).s₀)) ≫
              biprod.fst := by rw [Category.comp_id]
    · calc (biprod.inl ≫ (splitInv T ≫ splitMap T)) ≫ biprod.snd
          = biprod.inl ≫ (splitInv T ≫ (splitMap T ≫ biprod.snd)) := by
              rw [Category.assoc, Category.assoc]
        _ = biprod.inl ≫ (splitInv T ≫ Work.ATOM.qred T (Work.ATOM.levelData T).s₀) := by
              rw [splitMap_snd]
        _ = (biprod.inl ≫ splitInv T) ≫ Work.ATOM.qred T (Work.ATOM.levelData T).s₀ :=
              (Category.assoc _ _ _).symm
        _ = Work.ATOM.zmap (Work.ATOM.ptAt (Work.ATOM.levelData T).s₀) ≫
              Work.ATOM.qred T (Work.ATOM.levelData T).s₀ := by
              rw [splitInv, CategoryTheory.Limits.biprod.inl_desc]
        _ = 0 := zmap_ptAt_qred T
        _ = biprod.inl ≫ biprod.snd := (CategoryTheory.Limits.biprod.inl_snd).symm
        _ = (biprod.inl ≫ 𝟙 (zf Work.ATOM.pt ⊞ Work.ATOM.zred T (Work.ATOM.levelData T).s₀)) ≫
              biprod.snd := by rw [Category.comp_id]
  · apply CategoryTheory.Limits.biprod.hom_ext
    · calc (biprod.inr ≫ (splitInv T ≫ splitMap T)) ≫ biprod.fst
          = biprod.inr ≫ (splitInv T ≫ (splitMap T ≫ biprod.fst)) := by
              rw [Category.assoc, Category.assoc]
        _ = biprod.inr ≫ (splitInv T ≫ Work.ATOM.aug T) := by rw [splitMap_fst]
        _ = (biprod.inr ≫ splitInv T) ≫ Work.ATOM.aug T := (Category.assoc _ _ _).symm
        _ = splitSec T ≫ Work.ATOM.aug T := by
              rw [splitInv, CategoryTheory.Limits.biprod.inr_desc]
        _ = 0 := splitSec_aug T
        _ = biprod.inr ≫ biprod.fst := (CategoryTheory.Limits.biprod.inr_fst).symm
        _ = (biprod.inr ≫ 𝟙 (zf Work.ATOM.pt ⊞ Work.ATOM.zred T (Work.ATOM.levelData T).s₀)) ≫
              biprod.fst := by rw [Category.comp_id]
    · calc (biprod.inr ≫ (splitInv T ≫ splitMap T)) ≫ biprod.snd
          = biprod.inr ≫ (splitInv T ≫ (splitMap T ≫ biprod.snd)) := by
              rw [Category.assoc, Category.assoc]
        _ = biprod.inr ≫ (splitInv T ≫ Work.ATOM.qred T (Work.ATOM.levelData T).s₀) := by
              rw [splitMap_snd]
        _ = (biprod.inr ≫ splitInv T) ≫ Work.ATOM.qred T (Work.ATOM.levelData T).s₀ :=
              (Category.assoc _ _ _).symm
        _ = splitSec T ≫ Work.ATOM.qred T (Work.ATOM.levelData T).s₀ := by
              rw [splitInv, CategoryTheory.Limits.biprod.inr_desc]
        _ = 𝟙 (Work.ATOM.zred T (Work.ATOM.levelData T).s₀) := splitSec_qred T
        _ = biprod.inr ≫ biprod.snd := (CategoryTheory.Limits.biprod.inr_snd).symm
        _ = (biprod.inr ≫ 𝟙 (zf Work.ATOM.pt ⊞ Work.ATOM.zred T (Work.ATOM.levelData T).s₀)) ≫
              biprod.snd := by rw [Category.comp_id]

theorem splitMap_isIso (T : LightProfinite.{0}) [Infinite T] : IsIso (splitMap T) :=
  IsIso.mk ⟨splitInv T, splitMap_comp_splitInv T, splitInv_comp_splitMap T⟩

/-! ## The infinite case: comparison with a biproduct of solid-equivalences -/

/-- **The infinite case of `doubleDualUnit_solidEquiv`**, given the product structure on
`dd (ℤ[T])` (the Haar basis) and the solid-equivalence of the Haar coordinate map. -/
theorem solidEquiv_of_prod (T : LightProfinite.{0}) [Infinite T]
    (e : dd (zf T) ≅ (𝟙_ LightCondAb ⊞ Work.ANALYTIC.prodZ))
    (he₁ : e.hom ≫ CategoryTheory.Limits.biprod.fst = coordMap (zf T) (lamInf T))
    (he₂ : ∀ j : ℕ, e.hom ≫ CategoryTheory.Limits.biprod.snd ≫
      CategoryTheory.Limits.Pi.π (fun _ : ℕ => 𝟙_ LightCondAb) j = coordMap (zf T) (lamJ T j))
    (hk : Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map (kMap T))) :
    Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map (doubleDualUnit (zf T))) := by
  have hdiag : Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map
        (CategoryTheory.Limits.biprod.map
          (Work.ATOM.unitIso.inv : zf Work.ATOM.pt ⟶ 𝟙_ LightCondAb) (kMap T))) :=
    Work.ANALYTIC.solidEquiv_biprod Work.ANALYTIC.toolkitProp _ _ _ _ _ _
      (Work.ANALYTIC.toolkitProp.of_iso _ (inferInstance)) hk
  have hcomp : splitMap T ≫ CategoryTheory.Limits.biprod.map
        (Work.ATOM.unitIso.inv : zf Work.ATOM.pt ⟶ 𝟙_ LightCondAb) (kMap T) =
      doubleDualUnit (zf T) ≫ e.hom := by
    apply CategoryTheory.Limits.biprod.hom_ext
    · calc (splitMap T ≫ CategoryTheory.Limits.biprod.map
              (Work.ATOM.unitIso.inv : zf Work.ATOM.pt ⟶ 𝟙_ LightCondAb) (kMap T)) ≫
            CategoryTheory.Limits.biprod.fst
          = splitMap T ≫ (CategoryTheory.Limits.biprod.map
              (Work.ATOM.unitIso.inv : zf Work.ATOM.pt ⟶ 𝟙_ LightCondAb) (kMap T) ≫
                CategoryTheory.Limits.biprod.fst) := Category.assoc _ _ _
        _ = splitMap T ≫ (CategoryTheory.Limits.biprod.fst ≫
              (Work.ATOM.unitIso.inv : zf Work.ATOM.pt ⟶ 𝟙_ LightCondAb)) := by
              rw [CategoryTheory.Limits.biprod.map_fst]
        _ = (splitMap T ≫ CategoryTheory.Limits.biprod.fst) ≫
              (Work.ATOM.unitIso.inv : zf Work.ATOM.pt ⟶ 𝟙_ LightCondAb) :=
              (Category.assoc _ _ _).symm
        _ = Work.ATOM.aug T ≫ (Work.ATOM.unitIso.inv : zf Work.ATOM.pt ⟶ 𝟙_ LightCondAb) := by
              rw [splitMap_fst]
        _ = lamInf T := rfl
        _ = doubleDualUnit (zf T) ≫ coordMap (zf T) (lamInf T) :=
              (doubleDualUnit_coord (zf T) (lamInf T)).symm
        _ = doubleDualUnit (zf T) ≫ (e.hom ≫ CategoryTheory.Limits.biprod.fst) := by rw [he₁]
        _ = (doubleDualUnit (zf T) ≫ e.hom) ≫ CategoryTheory.Limits.biprod.fst :=
              Category.assoc _ _ _
    · apply CategoryTheory.Limits.Pi.hom_ext
      intro j
      calc ((splitMap T ≫ CategoryTheory.Limits.biprod.map
              (Work.ATOM.unitIso.inv : zf Work.ATOM.pt ⟶ 𝟙_ LightCondAb) (kMap T)) ≫
            CategoryTheory.Limits.biprod.snd) ≫
            CategoryTheory.Limits.Pi.π (fun _ : ℕ => 𝟙_ LightCondAb) j
          = splitMap T ≫ (CategoryTheory.Limits.biprod.map
              (Work.ATOM.unitIso.inv : zf Work.ATOM.pt ⟶ 𝟙_ LightCondAb) (kMap T) ≫
                (CategoryTheory.Limits.biprod.snd ≫
                  CategoryTheory.Limits.Pi.π (fun _ : ℕ => 𝟙_ LightCondAb) j)) := by
              rw [Category.assoc, Category.assoc]
        _ = splitMap T ≫ ((CategoryTheory.Limits.biprod.map
              (Work.ATOM.unitIso.inv : zf Work.ATOM.pt ⟶ 𝟙_ LightCondAb) (kMap T) ≫
                CategoryTheory.Limits.biprod.snd) ≫
                CategoryTheory.Limits.Pi.π (fun _ : ℕ => 𝟙_ LightCondAb) j) := by
              rw [Category.assoc]
        _ = splitMap T ≫ ((CategoryTheory.Limits.biprod.snd ≫ kMap T) ≫
                CategoryTheory.Limits.Pi.π (fun _ : ℕ => 𝟙_ LightCondAb) j) := by
              rw [CategoryTheory.Limits.biprod.map_snd]
        _ = splitMap T ≫ (CategoryTheory.Limits.biprod.snd ≫ (kMap T ≫
                CategoryTheory.Limits.Pi.π (fun _ : ℕ => 𝟙_ LightCondAb) j)) := by
              rw [Category.assoc]
        _ = (splitMap T ≫ CategoryTheory.Limits.biprod.snd) ≫ (kMap T ≫
                CategoryTheory.Limits.Pi.π (fun _ : ℕ => 𝟙_ LightCondAb) j) :=
              (Category.assoc _ _ _).symm
        _ = Work.ATOM.qred T (Work.ATOM.levelData T).s₀ ≫ (kMap T ≫
                CategoryTheory.Limits.Pi.π (fun _ : ℕ => 𝟙_ LightCondAb) j) := by
              rw [splitMap_snd]
        _ = lamJ T j := qred_kMap_π T j
        _ = doubleDualUnit (zf T) ≫ coordMap (zf T) (lamJ T j) :=
              (doubleDualUnit_coord (zf T) (lamJ T j)).symm
        _ = doubleDualUnit (zf T) ≫ (e.hom ≫ CategoryTheory.Limits.biprod.snd ≫
                CategoryTheory.Limits.Pi.π (fun _ : ℕ => 𝟙_ LightCondAb) j) := by rw [he₂ j]
        _ = ((doubleDualUnit (zf T) ≫ e.hom) ≫ CategoryTheory.Limits.biprod.snd) ≫
                CategoryTheory.Limits.Pi.π (fun _ : ℕ => 𝟙_ LightCondAb) j := by
              rw [Category.assoc, Category.assoc]
  haveI : IsIso (splitMap T) := splitMap_isIso T
  have hsplit : Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map (splitMap T)) :=
    Work.ANALYTIC.toolkitProp.of_iso _ (Functor.map_isIso _ _)
  have hL : Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map
        (splitMap T ≫ CategoryTheory.Limits.biprod.map
          (Work.ATOM.unitIso.inv : zf Work.ATOM.pt ⟶ 𝟙_ LightCondAb) (kMap T))) := by
    rw [Functor.map_comp]
    exact Work.ANALYTIC.toolkitProp.comp _ _ hsplit hdiag
  rw [hcomp] at hL
  haveI : IsIso (e.hom) := e.isIso_hom
  refine Work.ANALYTIC.toolkitProp.of_comp_right
    ((DerivedCategory.singleFunctor LightCondAb 0).map (doubleDualUnit (zf T)))
    ((DerivedCategory.singleFunctor LightCondAb 0).map (e.hom)) ?_ ?_
  · exact Work.ANALYTIC.toolkitProp.of_iso _ (Functor.map_isIso _ _)
  · simpa only [Functor.map_comp] using hL

/-! ## The finite case -/

/-- **The finite case**: for a finite light profinite set, `ℤ[T]` is a finite free module, hence
dualizable, and the double-dual unit is an isomorphism. -/
theorem isIso_doubleDualUnit_of_finite (T : LightProfinite.{0}) [Finite T]
    (h : ∀ (J : Type) [Fintype J], IsIso (doubleDualUnit (∐ (fun _ : J => 𝟙_ LightCondAb)))) :
    IsIso (doubleDualUnit (zf T)) := by
  haveI : Fintype ↥T.toTop := Fintype.ofFinite _
  obtain ⟨e⟩ := Work.ANALYTIC.finite_iso_sigma_pt T
  let E : zf T ≅ ∐ (fun _ : ↥T => Work.ANALYTIC.Z) := Work.ANALYTIC.zfreeIsoSigma T e
  haveI hJ : IsIso (doubleDualUnit (∐ (fun _ : ↥T => 𝟙_ LightCondAb))) := h ↥T
  haveI hJZ : IsIso (doubleDualUnit (∐ (fun _ : ↥T => Work.ANALYTIC.Z))) := hJ
  haveI : IsIso (E.hom) := E.isIso_hom
  haveI : IsIso (ddFMap E.hom) := Functor.map_isIso ddF E.hom
  have hstep : E.hom ≫ doubleDualUnit (∐ (fun _ : ↥T => Work.ANALYTIC.Z)) =
      doubleDualUnit (zf T) ≫ ddFMap E.hom :=
    doubleDualUnit_natural E.hom
  have h5 : doubleDualUnit (zf T) =
      E.hom ≫ doubleDualUnit (∐ (fun _ : ↥T => Work.ANALYTIC.Z)) ≫ inv (ddFMap E.hom) := by
    rw [← Category.assoc, hstep, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [h5]
  infer_instance

end

theorem doubleDualUnit_solidEquiv (T : LightProfinite.{0}) :
    Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map
        (Work.ANALYTIC.CechPt.doubleDualUnit
          ((LightCondensed.free (R := ℤ)).obj T.toCondensed))) := by
  by_cases hT : Finite T
  · haveI : Finite T := hT
    haveI : IsIso (doubleDualUnit (zf T)) :=
      isIso_doubleDualUnit_of_finite T
        (fun J _ => Work.ANALYTIC.CechPt.doubleDualUnit_sigma_unit J)
    exact Work.ANALYTIC.toolkitProp.of_iso _ (Functor.map_isIso _ _)
  · haveI : Infinite T := not_finite_iff_infinite.mp hT
    exact solidEquiv_of_prod T
      (Classical.choose (Work.ANALYTIC.CechPt.ddZf_iso_prod T))
      (Classical.choose_spec (Work.ANALYTIC.CechPt.ddZf_iso_prod T)).1
      (Classical.choose_spec (Work.ANALYTIC.CechPt.ddZf_iso_prod T)).2
      (Work.ANALYTIC.CechPt.kMap_solidEquiv T)

end Work.ANALYTIC.CechPt

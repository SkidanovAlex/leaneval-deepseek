import Mathlib
import Submission.Work.LerayHirsch.LhGlueDefs
import Submission.Work.Thom.thomClass_of_cover
import Submission.Work.Thom.Ladder2

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Work.LerayHirsch

open CategoryTheory CategoryTheory.Limits
open Work.Thom

noncomputable section

/-! ## The two inclusions of the overlap, read through `pdIncl` -/

/-- The inclusion `U ∩ V ↪ U` of the two-piece cover, read through the pair-inclusion
`pdIncl`, is the continuous map `mvInclLeft`. -/
lemma hom_pdIncl_inter_left {X : Type} [TopologicalSpace X] (U V : Set X) :
    TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of X) U (U ∩ V)
      Set.inter_subset_left) = mvInclLeft U V := rfl

/-- The inclusion `U ∩ V ↪ V` of the two-piece cover, read through the pair-inclusion
`pdIncl`, is the continuous map `mvInclRight`. -/
lemma hom_pdIncl_inter_right {X : Type} [TopologicalSpace X] (U V : Set X) :
    TopCat.Hom.hom (Work.Cohomology.pdIncl (M := TopCat.of X) V (U ∩ V)
      Set.inter_subset_right) = mvInclRight U V := rfl

/-- Naturality of `pdCohMap` for the inclusion `U ∩ V ↪ U`, phrased with `mvInclLeft`. -/
lemma pdCohMap_mvInclLeft {X : Type} [TopologicalSpace X] (U V : Set X) (k : ℕ) :
    Work.Cohomology.pdCohMap (TopCat.of X) (∅ : Set X) U (U ∩ V) Set.inter_subset_left k
        ≫ (pdCohIso ↥(U ∩ V) k).hom
      = (pdCohIso ↥U k).hom ≫ CohMap (mvInclLeft U V) ℤ k := by
  have h := Work.Thom.pdCohMap_pdCohIso (B := X) U (U ∩ V) Set.inter_subset_left k
  rwa [hom_pdIncl_inter_left U V] at h

/-- Naturality of `pdCohMap` for the inclusion `U ∩ V ↪ V`, phrased with `mvInclRight`. -/
lemma pdCohMap_mvInclRight {X : Type} [TopologicalSpace X] (U V : Set X) (k : ℕ) :
    Work.Cohomology.pdCohMap (TopCat.of X) (∅ : Set X) V (U ∩ V) Set.inter_subset_right k
        ≫ (pdCohIso ↥(U ∩ V) k).hom
      = (pdCohIso ↥V k).hom ≫ CohMap (mvInclRight U V) ℤ k := by
  have h := Work.Thom.pdCohMap_pdCohIso (B := X) V (U ∩ V) Set.inter_subset_right k
  rwa [hom_pdIncl_inter_right U V] at h

/-! ## The two components of `mv2F` -/

/-- The first component of `mv2_components`: `mv2F` followed by the first projection is the
restriction to `U`. -/
lemma mv2F_comp_fst {X : Type} [TopologicalSpace X] (U V : Set X) (k : ℕ) :
    mv2F U V k ≫ (biprod.fst (X := Coh ℤ k ↥U) (Y := Coh ℤ k ↥V)) = restrCoh U ℤ k := by
  unfold mv2F
  simp only [Category.assoc]
  rw [biprod.mapIso_hom, biprod.map_fst]
  erw [Work.Thom.honestF_fst'_assoc]
  rw [Work.Thom.pdCohRes_pdCohIso]
  have h1 := Iso.inv_hom_id (pdCohIso X k)
  rw [← Category.assoc, h1, Category.id_comp]

/-- The second component of `mv2_components`: `mv2F` followed by the second projection is the
restriction to `V`. -/
lemma mv2F_comp_snd {X : Type} [TopologicalSpace X] (U V : Set X) (k : ℕ) :
    mv2F U V k ≫ (biprod.snd (X := Coh ℤ k ↥U) (Y := Coh ℤ k ↥V)) = restrCoh V ℤ k := by
  unfold mv2F
  simp only [Category.assoc]
  rw [biprod.mapIso_hom, biprod.map_snd]
  erw [Work.Thom.honestF_snd'_assoc]
  rw [Work.Thom.pdCohRes_pdCohIso]
  have h1 := Iso.inv_hom_id (pdCohIso X k)
  rw [← Category.assoc, h1, Category.id_comp]

/-! ## The two components of `mv2G`

To keep the rewriting purely syntactic we re-type the comparison isomorphism `pdCohIso` so that its
source is the relative cohomology `pdCohSub` (which is what `honestG` is stated with), and define a
copy `mv2G'` of `mv2G` in terms of it.  The two are equal by `rfl`. -/

/-- `pdCohIso` re-typed with `pdCohSub` as its source. -/
noncomputable def pdCohIsoSub {X : Type} [TopologicalSpace X] (U : Set X) (k : ℕ) :
    Work.Cohomology.pdCohSub (TopCat.of X) (∅ : Set X) U k ≅ Coh ℤ k ↥U :=
  pdCohIso ↥U k

/-- `mv2G` with the sources of its biproducts expressed through `pdCohSub`. -/
noncomputable def mv2G' {X : Type} [TopologicalSpace X] (U V : Set X) (k : ℕ) :
    Coh ℤ k ↥U ⊞ Coh ℤ k ↥V ⟶ Coh ℤ k ↥(U ∩ V) :=
  (biprod.mapIso (pdCohIsoSub U k) (pdCohIsoSub V k)).inv
    ≫ Work.Cohomology.honestG (TopCat.of X) (∅ : Set X) U V k
    ≫ (pdCohIso ↥(U ∩ V) k).hom

lemma mv2G'_eq {X : Type} [TopologicalSpace X] (U V : Set X) (k : ℕ) :
    mv2G' U V k = mv2G U V k := rfl

/-- The third component of `mv2_components` for the re-typed copy `mv2G'`. -/
lemma mv2G'_inl {X : Type} [TopologicalSpace X] (U V : Set X) (k : ℕ) :
    (biprod.inl (X := Coh ℤ k ↥U) (Y := Coh ℤ k ↥V)) ≫ mv2G' U V k
      = CohMap (mvInclLeft U V) ℤ k := by
  unfold mv2G'
  simp only [Category.assoc]
  rw [← Category.assoc, ← Category.assoc]
  rw [biprod.mapIso_inv, biprod.inl_map]
  rw [Category.assoc, Category.assoc]
  rw [Work.Thom.honestG_inl'_assoc]
  rw [pdCohMap_mvInclLeft]
  have h1 : (pdCohIsoSub U k).inv ≫ (pdCohIso ↥U k).hom = 𝟙 (Coh ℤ k ↥U) :=
    Iso.inv_hom_id (pdCohIso ↥U k)
  rw [← Category.assoc, h1, Category.id_comp]

/-- The fourth component of `mv2_components` for the re-typed copy `mv2G'`. -/
lemma mv2G'_inr {X : Type} [TopologicalSpace X] (U V : Set X) (k : ℕ) :
    (biprod.inr (X := Coh ℤ k ↥U) (Y := Coh ℤ k ↥V)) ≫ mv2G' U V k
      = -(CohMap (mvInclRight U V) ℤ k) := by
  unfold mv2G'
  simp only [Category.assoc]
  rw [← Category.assoc, ← Category.assoc]
  rw [biprod.mapIso_inv, biprod.inr_map]
  rw [Category.assoc, Category.assoc]
  rw [Work.Thom.honestG_inr'_assoc]
  rw [Preadditive.neg_comp]
  rw [pdCohMap_mvInclRight]
  rw [Preadditive.comp_neg]
  have h1 : (pdCohIsoSub V k).inv ≫ (pdCohIso ↥V k).hom = 𝟙 (Coh ℤ k ↥V) :=
    Iso.inv_hom_id (pdCohIso ↥V k)
  rw [← Category.assoc, h1, Category.id_comp]

/-- The third component of `mv2_components`: `biprod.inl` followed by `mv2G`. -/
lemma mv2G_inl {X : Type} [TopologicalSpace X] (U V : Set X) (k : ℕ) :
    (biprod.inl (X := Coh ℤ k ↥U) (Y := Coh ℤ k ↥V)) ≫ mv2G U V k
      = CohMap (mvInclLeft U V) ℤ k := by
  rw [← mv2G'_eq U V k]
  exact mv2G'_inl U V k

/-- The fourth component of `mv2_components`: `biprod.inr` followed by `mv2G`. -/
lemma mv2G_inr {X : Type} [TopologicalSpace X] (U V : Set X) (k : ℕ) :
    (biprod.inr (X := Coh ℤ k ↥U) (Y := Coh ℤ k ↥V)) ≫ mv2G U V k
      = -(CohMap (mvInclRight U V) ℤ k) := by
  rw [← mv2G'_eq U V k]
  exact mv2G'_inr U V k

theorem mv2_components {X : Type} [TopologicalSpace X] (U V : Set X) (k : ℕ) : CategoryTheory.CategoryStruct.comp (Work.LerayHirsch.mv2F U V k) (CategoryTheory.Limits.biprod.fst (X := Work.Thom.Coh ℤ k ↥U) (Y := Work.Thom.Coh ℤ k ↥V)) = Work.Thom.restrCoh U ℤ k ∧ CategoryTheory.CategoryStruct.comp (Work.LerayHirsch.mv2F U V k) (CategoryTheory.Limits.biprod.snd (X := Work.Thom.Coh ℤ k ↥U) (Y := Work.Thom.Coh ℤ k ↥V)) = Work.Thom.restrCoh V ℤ k ∧ CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.biprod.inl (X := Work.Thom.Coh ℤ k ↥U) (Y := Work.Thom.Coh ℤ k ↥V)) (Work.LerayHirsch.mv2G U V k) = Work.Thom.CohMap (Work.LerayHirsch.mvInclLeft U V) ℤ k ∧ CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.biprod.inr (X := Work.Thom.Coh ℤ k ↥U) (Y := Work.Thom.Coh ℤ k ↥V)) (Work.LerayHirsch.mv2G U V k) = -(Work.Thom.CohMap (Work.LerayHirsch.mvInclRight U V) ℤ k) :=
  ⟨mv2F_comp_fst U V k, mv2F_comp_snd U V k, mv2G_inl U V k, mv2G_inr U V k⟩

end

end Work.LerayHirsch

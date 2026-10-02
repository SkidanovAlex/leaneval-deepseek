import Mathlib
import Submission.Work.ThomBordism.RelDuality.Supp2
import Submission.Work.Orient.Boundary.localHomology_corner

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold Topology

namespace Work.ThomBordism.RelDuality

noncomputable section

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 9) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M] [CompactSpace M] [T2Space M]
  [T2Space (Double 8 M)] [CompactSpace (Double 8 M)]
  [ChartedSpace (EuclideanSpace ℝ (Fin 9)) (Double 8 M)]

/-- The interior of `M` is open in `M`. -/
theorem isOpen_intSet : IsOpen (DoubleFC.intSet 8 M) := by
  rw [DoubleFC.intSet]
  exact (Work.ThomBordism.isClosed_boundary_one (n := 8) (M := M)).isOpen_compl

/-- The two pairs `(int M, int M ∖ suppOf L)` and `(intImg, intImg ∖ L)` correspond under `eInt`. -/
theorem eInt_mem_iff (L : Set (Double 8 M)) (z : DoubleFC.intSet 8 M) :
    z ∈ ({z : DoubleFC.intSet 8 M | (z : M) ∈ (suppOf (M := M) L)ᶜ} : Set _) ↔
      DoubleFC.eInt 8 M z ∈ {v : DoubleFC.intImg 8 M | (v : Double 8 M) ∈ Lᶜ} := by
  show (z : M) ∈ (suppOf (M := M) L)ᶜ ↔
    ((DoubleFC.eInt 8 M z : DoubleFC.intImg 8 M) : Double 8 M) ∈ Lᶜ
  rw [DoubleFC.eInt_apply_coe]
  exact Iff.rfl

/-- The restricted homeomorphism `int M ∖ suppOf L ≃ intImg ∖ L`. -/
noncomputable def eIntSub (L : Set (Double 8 M)) :
    ↥({z : DoubleFC.intSet 8 M | (z : M) ∈ (suppOf (M := M) L)ᶜ} : Set _) ≃ₜ
      ↥({v : DoubleFC.intImg 8 M | (v : Double 8 M) ∈ Lᶜ} : Set _) :=
  Work.Orient.Boundary.homeomorphRestrict (DoubleFC.eInt 8 M) _ _ (eInt_mem_iff L)

/-- The restricted inverse of the open embedding `int M → D`, as a map of `TopCat`. -/
noncomputable abbrev imgToIntSub (L : Set (Double 8 M)) :
    TopCat.of ({v : DoubleFC.intImg 8 M | (v : Double 8 M) ∈ Lᶜ} : Set _) ⟶
      TopCat.of ({z : DoubleFC.intSet 8 M | (z : M) ∈ (suppOf (M := M) L)ᶜ} : Set _) :=
  TopCat.ofHom (eIntSub (M := M) L).symm.toHomotopyEquiv.toFun

/-- The compatibility of `imgToInt` with the restricted maps. -/
theorem imgToIntSub_spec (L : Set (Double 8 M)) :
    Work.Cohomology.subtypeIncl (TopCat.of (DoubleFC.intImg 8 M))
        ({v : DoubleFC.intImg 8 M | (v : Double 8 M) ∈ Lᶜ} : Set _)
      ≫ imgToInt (M := M)
      = imgToIntSub (M := M) L
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (DoubleFC.intSet 8 M))
            ({z : DoubleFC.intSet 8 M | (z : M) ∈ (suppOf (M := M) L)ᶜ} : Set _) := by
  ext z
  rfl

/-- `imgToInt` is the map underlying the homeomorphism `eInt.symm`. -/
theorem imgToInt_eq :
    imgToInt (M := M)
      = TopCat.ofHom (DoubleFC.eInt 8 M).symm.toHomotopyEquiv.toFun := by
  ext z
  rfl

/-- **The factorization of `imgPairMap`** through the interior of `M` and the excision. -/
theorem imgPairMap_eq (L : Set (Double 8 M))
    (h : ∀ x ∈ ({z : DoubleFC.intImg 8 M | (z : Double 8 M) ∈ Lᶜ} : Set _),
      imgInv (M := M) x ∈ (suppOf (M := M) L)ᶜ) :
    imgPairMap (M := M) L (suppOf (M := M) L) h
      = (Work.Cohomology.relChainsMapOf (TopCat.of (DoubleFC.intImg 8 M))
            (TopCat.of (DoubleFC.intSet 8 M))
            ({v : DoubleFC.intImg 8 M | (v : Double 8 M) ∈ Lᶜ} : Set _)
            ({z : DoubleFC.intSet 8 M | (z : M) ∈ (suppOf (M := M) L)ᶜ} : Set _)
            (imgToInt (M := M)) (imgToIntSub (M := M) L) (imgToIntSub_spec (M := M) L))
        ≫ (Work.Cohomology.relChainsMap (TopCat.of M) (DoubleFC.intSet 8 M)
            ((suppOf (M := M) L)ᶜ)) := by
  refine (cancel_epi (CategoryTheory.Limits.cokernel.π
    (Work.Cohomology.inclChains (TopCat.of (DoubleFC.intImg 8 M))
      ({v : DoubleFC.intImg 8 M | (v : Double 8 M) ∈ Lᶜ} : Set _)))).1 ?_
  rw [imgPairMap_π]
  conv_rhs => rw [← Category.assoc, Work.Cohomology.capRel_cokernel_π_relChainsMapOf]
  conv_rhs => rw [Category.assoc]
  erw [Work.Cohomology.cokernel_π_relChainsMap (TopCat.of M) (DoubleFC.intSet 8 M)
    ((suppOf (M := M) L)ᶜ)]
  rw [← Category.assoc, ← Work.Cohomology.chainMap_comp_relChains]

/-- The restricted inverse of the open embedding induces a quasi-isomorphism of chain complexes. -/
theorem isIso_homologyMap_chainMap_imgToIntSub (L : Set (Double 8 M)) (j : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ
        (TopCat.of ({v : DoubleFC.intImg 8 M | (v : Double 8 M) ∈ Lᶜ} : Set _))
        (TopCat.of ({z : DoubleFC.intSet 8 M | (z : M) ∈ (suppOf (M := M) L)ᶜ} : Set _))
        (imgToIntSub (M := M) L)) j) :=
  Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv
    (X := TopCat.of ({v : DoubleFC.intImg 8 M | (v : Double 8 M) ∈ Lᶜ} : Set _))
    (Y := TopCat.of ({z : DoubleFC.intSet 8 M | (z : M) ∈ (suppOf (M := M) L)ᶜ} : Set _))
    (eIntSub (M := M) L).symm.toHomotopyEquiv j

/-- **`imgPairMap` is an isomorphism in degree `9`.** -/
theorem imgPairMap_isIso (L : Set (Double 8 M)) (hLc : IsClosed L)
    (hsub : L ⊆ DoubleFC.intImg 8 M)
    (h : ∀ x ∈ ({z : DoubleFC.intImg 8 M | (z : Double 8 M) ∈ Lᶜ} : Set _),
      imgInv (M := M) x ∈ (suppOf (M := M) L)ᶜ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (imgPairMap (M := M) L (suppOf (M := M) L) h) 9) := by
  have hKc : IsClosed (suppOf (M := M) L) := hLc.preimage (continuous_doubleιM (n := 8) (M := M))
  have hKsub : suppOf (M := M) L ⊆ DoubleFC.intSet 8 M := by
    intro x hx
    have h1 : x ∈ suppOf (M := M) (DoubleFC.intImg 8 M) := suppOf_mono hsub hx
    rwa [suppOf_intImg] at h1
  have hcov : DoubleFC.intSet 8 M ∪ ((suppOf (M := M) L)ᶜ) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    by_cases hx : x ∈ suppOf (M := M) L
    · exact Or.inl (hKsub hx)
    · exact Or.inr hx
  haveI hR1 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf (TopCat.of (DoubleFC.intImg 8 M))
        (TopCat.of (DoubleFC.intSet 8 M))
        ({v : DoubleFC.intImg 8 M | (v : Double 8 M) ∈ Lᶜ} : Set _)
        ({z : DoubleFC.intSet 8 M | (z : M) ∈ (suppOf (M := M) L)ᶜ} : Set _)
        (imgToInt (M := M)) (imgToIntSub (M := M) L) (imgToIntSub_spec (M := M) L)) 9) :=
    Work.Cohomology.relChainsMapOf_isIso _ _ _ _ _ 9
      (fun k => by
        rw [imgToInt_eq (M := M)]
        exact Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv
          (X := TopCat.of (DoubleFC.intImg 8 M)) (Y := TopCat.of (DoubleFC.intSet 8 M))
          (DoubleFC.eInt 8 M).symm.toHomotopyEquiv k)
      (fun k => isIso_homologyMap_chainMap_imgToIntSub (M := M) L k)
  haveI hR2 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMap (TopCat.of M) (DoubleFC.intSet 8 M)
        ((suppOf (M := M) L)ᶜ)) 9) :=
    Work.Cohomology.excision_relChainsMap_isIso (TopCat.of M) (DoubleFC.intSet 8 M)
      ((suppOf (M := M) L)ᶜ) (isOpen_intSet (M := M)) hKc.isOpen_compl hcov 9
  rw [imgPairMap_eq (M := M) L h, HomologicalComplex.homologyMap_comp]
  infer_instance

/-- **The image of the local fundamental class of `cD` under the inverse of the open embedding is
the image of `w` under `bdryIncl`.** -/
theorem localFundClass_image_eq
    (w : (Work.Cohomology.relChains (TopCat.of M) (bdry9 M)).homology 9)
    (cD : (Work.Cohomology.singularChains ℤ (TopCat.of (Double 8 M))).homology 9)
    (hM : ∀ (y : M) (hy : y ∉ bdry9 M),
      Work.ThomBordism.localClassAt (TopCat.of (Double 8 M)) 9 cD (doubleιM y)
        = (HomologicalComplex.homologyMap (DoubleFC.pairMapιM 8 M y) 9)
            (RelDoubleClass.locW (n := 8) (M := M) w y hy)) :
    CompHyp (M := M) w cD := by
  intro β s B y hball hx hsub
  have hLc : IsCompact (⋃ b ∈ s, B b) :=
    s.isCompact_biUnion (fun b hb => (hball b hb).isCompact)
  have hpair := compWitness (M := M) (⋃ b ∈ s, B b)
  have hObs : SuppObs (M := M) (suppOf (M := M) (⋃ b ∈ s, B b)) (⋃ b ∈ s, B b) :=
    fun z hz hzL => hz hzL
  have hsq := relChainsMap_img_eq (M := M) (⋃ b ∈ s, B b)
    (suppOf (M := M) (⋃ b ∈ s, B b)) rfl hpair hObs
  have hsqH := congrArg (fun φ => HomologicalComplex.homologyMap φ 9) hsq
  rw [HomologicalComplex.homologyMap_comp] at hsqH
  have hcov : DoubleFC.intImg 8 M ∪ ((⋃ b ∈ s, B b)ᶜ : Set (Double 8 M)) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro z
    by_cases hz : z ∈ ⋃ b ∈ s, B b
    · exact Or.inl (hsub hz)
    · exact Or.inr hz
  haveI hisoC : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMap (TopCat.of (Double 8 M)) (DoubleFC.intImg 8 M)
        ((⋃ b ∈ s, B b)ᶜ : Set (Double 8 M))) 9) :=
    Work.Cohomology.excision_relChainsMap_isIso (TopCat.of (Double 8 M))
      (DoubleFC.intImg 8 M) ((⋃ b ∈ s, B b)ᶜ) (isOpen_intImg (M := M))
      hLc.isClosed.isOpen_compl hcov 9
  -- the two chain maps
  set A := HomologicalComplex.homologyMap
    (imgPairMap (M := M) (⋃ b ∈ s, B b) (suppOf (M := M) (⋃ b ∈ s, B b)) hpair) 9 with hAdef
  set Bm := HomologicalComplex.homologyMap
    (suppMap (M := M) (suppOf (M := M) (⋃ b ∈ s, B b)) (⋃ b ∈ s, B b) hObs) 9 with hBdef
  set Cc := HomologicalComplex.homologyMap
    (Work.Cohomology.relChainsMap (TopCat.of (Double 8 M)) (DoubleFC.intImg 8 M)
      ((⋃ b ∈ s, B b)ᶜ : Set (Double 8 M))) 9 with hCdef
  have hBA : ∀ u, Bm (A u) = Cc u := by
    intro u
    rw [hsqH]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  haveI hAiso : CategoryTheory.IsIso A := imgPairMap_isIso (M := M) (⋃ b ∈ s, B b)
    hLc.isClosed hsub hpair
  have hBeq : Bm = CategoryTheory.inv A ≫ Cc := by
    calc Bm = 𝟙 _ ≫ Bm := (Category.id_comp _).symm
      _ = (CategoryTheory.inv A ≫ A) ≫ Bm := by rw [IsIso.inv_hom_id]
      _ = CategoryTheory.inv A ≫ (A ≫ Bm) := Category.assoc _ _ _
      _ = CategoryTheory.inv A ≫ Cc := by rw [← hsqH]
  haveI hBiso : CategoryTheory.IsIso Bm := by
    rw [hBeq]; infer_instance
  have hinjB : Function.Injective (fun u => Bm u) :=
    (ModuleCat.mono_iff_injective Bm).mp (IsIso.mono_of_iso Bm)
  have hC : Cc (Work.Cohomology.localFundClass 9 cD (DoubleFC.intImg 8 M)
      (isOpen_intImg (M := M)) (⋃ b ∈ s, B b) hsub hLc)
      = Work.Cohomology.relLocClass (TopCat.of (Double 8 M)) 9 cD (⋃ b ∈ s, B b) :=
    Work.Cohomology.localFundClass_spec 9 cD (DoubleFC.intImg 8 M) (isOpen_intImg (M := M))
      (⋃ b ∈ s, B b) hsub hLc
  have hK : Work.Cohomology.relLocClass (TopCat.of (Double 8 M)) 9 cD (⋃ b ∈ s, B b)
      = Bm ((HomologicalComplex.homologyMap
          (bdryIncl (M := M) (suppOf (M := M) (⋃ b ∈ s, B b))
            (by
              intro z hz
              have h1 : z ∈ suppOf (M := M) (DoubleFC.intImg 8 M) := suppOf_mono hsub hz
              rw [suppOf_intImg] at h1
              exact h1)) 9) w) :=
    relLocClass_coordBalls (M := M) w cD hM s B y hball hx hsub
  have h1 : Bm (A (Work.Cohomology.localFundClass 9 cD (DoubleFC.intImg 8 M)
      (isOpen_intImg (M := M)) (⋃ b ∈ s, B b) hsub hLc))
      = Bm ((HomologicalComplex.homologyMap
          (bdryIncl (M := M) (suppOf (M := M) (⋃ b ∈ s, B b))
            (by
              intro z hz
              have h1 : z ∈ suppOf (M := M) (DoubleFC.intImg 8 M) := suppOf_mono hsub hz
              rw [suppOf_intImg] at h1
              exact h1)) 9) w) := by
    rw [hBA, hC, hK]
  exact hinjB h1

end

end Work.ThomBordism.RelDuality

import Mathlib
import Submission.Work.ThomBordism.RelDuality.Supp
import Submission.Work.ThomBordism.RelDuality.relLocClass_coordBalls
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Cohomology.relChainsMapOf_comp
import Submission.Work.Cohomology.relChainsMapOf_isIso
import Submission.Work.Cohomology.localCohomology
import Submission.Work.Cohomology.capRelAux
import Submission.Work.Cohomology.pd_middleDegree_of_good

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
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

/-- The interior of `M` is open in its double. -/
theorem isOpen_intImg : IsOpen (DoubleFC.intImg 8 M) := by
  rw [DoubleFC.intImg, ← Set.image_univ]
  exact (isOpenEmbedding_interiorEmb (n := 8) (M := M)).isOpenMap _ isOpen_univ

/-- The inverse of the open embedding `int M → D`, as a map to `int M`. -/
abbrev imgToInt :
    TopCat.of (DoubleFC.intImg 8 M) ⟶ TopCat.of (DoubleFC.intSet 8 M) :=
  TopCat.ofHom ⟨fun z => (DoubleFC.eInt 8 M).symm z, (DoubleFC.eInt 8 M).symm.continuous⟩

/-- The inverse of the open embedding `int M → D`, as a map to `M`. -/
abbrev imgInv : TopCat.of (DoubleFC.intImg 8 M) ⟶ TopCat.of M :=
  imgToInt (M := M) ≫ Work.Cohomology.subtypeIncl (TopCat.of M) (DoubleFC.intSet 8 M)

/-- The first copy inclusion inverts `imgInv`. -/
theorem dblIota_imgInv (z : DoubleFC.intImg 8 M) :
    doubleιM (imgInv (M := M) z) = (z : Double 8 M) := by
  change doubleιM (((DoubleFC.eInt 8 M).symm z : DoubleFC.intSet 8 M) : M) = (z : Double 8 M)
  rw [← DoubleFC.eInt_apply_coe 8 M ((DoubleFC.eInt 8 M).symm z)]
  rw [(DoubleFC.eInt 8 M).apply_symm_apply z]

theorem imgInv_comp_dblIota :
    imgInv (M := M) ≫ dblIota (M := M)
      = Work.Cohomology.subtypeIncl (TopCat.of (Double 8 M)) (DoubleFC.intImg 8 M) := by
  apply CategoryTheory.ConcreteCategory.hom_ext
  intro z
  exact dblIota_imgInv (M := M) z

/-- **The canonical witness** that the first-copy pair map carries the complement of `L` into the
complement of `suppOf L` (named so that the term can be reproduced verbatim elsewhere). -/
abbrev compWitness (L : Set (Double 8 M)) :
    ∀ x ∈ ({z : DoubleFC.intImg 8 M | (z : Double 8 M) ∈ Lᶜ} : Set _),
      imgInv (M := M) x ∈ (suppOf (M := M) L)ᶜ :=
  fun x hx hxK => hx (by rw [← dblIota_imgInv (M := M) x]; exact hxK)

/-- The pair map `(int M, int M∖L) → (M, M∖K)` induced by the inverse of the open embedding. -/
abbrev imgPairMap (L : Set (Double 8 M)) (K : Set M)
    (h : ∀ x ∈ ({z : DoubleFC.intImg 8 M | (z : Double 8 M) ∈ Lᶜ} : Set _),
      imgInv (M := M) x ∈ Kᶜ) :
    Work.Cohomology.relChains (TopCat.of (DoubleFC.intImg 8 M))
        {z : DoubleFC.intImg 8 M | (z : Double 8 M) ∈ Lᶜ} ⟶
      Work.Cohomology.relChains (TopCat.of M) (Kᶜ : Set M) :=
  Work.Cohomology.relChainsMapOf (TopCat.of (DoubleFC.intImg 8 M)) (TopCat.of M)
    {z : DoubleFC.intImg 8 M | (z : Double 8 M) ∈ Lᶜ} (Kᶜ : Set M)
    (imgInv (M := M))
    (Work.Cohomology.relMapSub {z : DoubleFC.intImg 8 M | (z : Double 8 M) ∈ Lᶜ} (Kᶜ : Set M)
      (imgInv (M := M)) h)
    (Work.Cohomology.relMapSub_spec _ _ _ h)

/-- The defining property of `imgPairMap`. -/
theorem imgPairMap_π (L : Set (Double 8 M)) (K : Set M)
    (h : ∀ x ∈ ({z : DoubleFC.intImg 8 M | (z : Double 8 M) ∈ Lᶜ} : Set _),
      imgInv (M := M) x ∈ Kᶜ) :
    CategoryTheory.Limits.cokernel.π
        (Work.Cohomology.inclChains (TopCat.of (DoubleFC.intImg 8 M))
          {z : DoubleFC.intImg 8 M | (z : Double 8 M) ∈ Lᶜ})
        ≫ imgPairMap (M := M) L K h
      = Work.Cohomology.chainMap ℤ (TopCat.of (DoubleFC.intImg 8 M)) (TopCat.of M)
          (imgInv (M := M))
        ≫ CategoryTheory.Limits.cokernel.π
            (Work.Cohomology.inclChains (TopCat.of M) (Kᶜ : Set M)) :=
  Work.Cohomology.capRel_cokernel_π_relChainsMapOf _ _ _ _ _

/-- **The pair map of the open embedding is the composite of `imgPairMap` and `suppMap`.** -/
theorem relChainsMap_img_eq (L : Set (Double 8 M)) (K : Set M) (hLK : K = suppOf (M := M) L)
    (h : ∀ x ∈ ({z : DoubleFC.intImg 8 M | (z : Double 8 M) ∈ Lᶜ} : Set _),
      imgInv (M := M) x ∈ Kᶜ)
    (hObs : SuppObs (M := M) K L) :
    Work.Cohomology.relChainsMap (TopCat.of (Double 8 M)) (DoubleFC.intImg 8 M)
        (Lᶜ : Set (Double 8 M))
      = imgPairMap (M := M) L K h ≫ suppMap (M := M) K L hObs := by
  refine (cancel_epi (CategoryTheory.Limits.cokernel.π
    (Work.Cohomology.inclChains (TopCat.of (DoubleFC.intImg 8 M))
      {z : DoubleFC.intImg 8 M | (z : Double 8 M) ∈ Lᶜ}))).1 ?_
  erw [Work.Cohomology.cokernel_π_relChainsMap (TopCat.of (Double 8 M)) (DoubleFC.intImg 8 M) (Lᶜ)]
  conv_rhs => rw [← Category.assoc, imgPairMap_π, Category.assoc]
  unfold suppMap
  rw [Work.Cohomology.capRel_cokernel_π_relChainsMapOf]
  conv_rhs => rw [← Category.assoc, ← Work.Cohomology.chainMap_comp_relChains]
  rw [imgInv_comp_dblIota (M := M)]

/-- **The composite identity (COMP)**, as a `Prop`: the image of the local fundamental class of
`cD` at a finite union of coordinate balls inside the interior of the first half, under the inverse
of the open embedding, is the image of `w` under `bdryIncl`. -/
def CompHyp (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 9) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M] [CompactSpace M] [T2Space M]
    [T2Space (Double 8 M)] [CompactSpace (Double 8 M)]
    [ChartedSpace (EuclideanSpace ℝ (Fin 9)) (Double 8 M)]
    (w : (Work.Cohomology.relChains (TopCat.of M) (bdry9 M)).homology 9)
    (cD : (Work.Cohomology.singularChains ℤ (TopCat.of (Double 8 M))).homology 9) : Prop :=
  ∀ {β : Type} (s : Finset β) (B : β → Set (Double 8 M)) (y : β → M)
    (hball : ∀ b ∈ s, IsCoordBall 9 (TopCat.of (Double 8 M)) (B b))
    (hx : ∀ b ∈ s, doubleιM (y b) ∈ B b)
    (hsub : (⋃ b ∈ s, B b) ⊆ DoubleFC.intImg 8 M),
    (HomologicalComplex.homologyMap
        (imgPairMap (M := M) (⋃ b ∈ s, B b) (suppOf (M := M) (⋃ b ∈ s, B b))
          (compWitness (M := M) (⋃ b ∈ s, B b))) 9)
        (Work.Cohomology.localFundClass 9 cD (DoubleFC.intImg 8 M) (isOpen_intImg (M := M))
          (⋃ b ∈ s, B b) hsub
          (s.isCompact_biUnion (fun b hb => (hball b hb).isCompact)))
      = (HomologicalComplex.homologyMap
          (bdryIncl (M := M) (suppOf (M := M) (⋃ b ∈ s, B b))
            (by
              intro z hz
              have h1 : z ∈ suppOf (M := M) (DoubleFC.intImg 8 M) := suppOf_mono hsub hz
              rw [suppOf_intImg] at h1
              exact h1)) 9) w

end

end Work.ThomBordism.RelDuality

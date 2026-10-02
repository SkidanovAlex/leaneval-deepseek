import Mathlib
import Submission.Work.ThomBordism.RelDuality.Supp3
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_goodD_natural
import Submission.Work.Cohomology.pd_middleDegree_of_good
import Submission.Work.Cohomology.Crux.relCapPair_natural
import Submission.Work.Cohomology.capRelAux
import Submission.Work.ThomBordism.doubleFC.interiorData
import Submission.Work.ThomBordism.localGenAux
import Submission.Work.Cohomology.hmv_naturality

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

/-- The excluded set of the pair `(int M, int M ∖ K)` inside the double. -/
abbrev Arel (K : Set (Double 8 M)) : Set (DoubleFC.intImg 8 M) :=
  {z : DoubleFC.intImg 8 M | (z : Double 8 M) ∈ Kᶜ}

/-- The same excluded set, on the `int M ⊆ M` side. -/
abbrev Brel (K : Set (Double 8 M)) : Set (DoubleFC.intSet 8 M) :=
  {z : DoubleFC.intSet 8 M | (z : M) ∈ (suppOf (M := M) K)ᶜ}

/-! ## Elementary helpers -/

/-- An isomorphism in `ModuleCat ℤ` is a bijective map. -/
theorem bijective_of_isIso {X Y : ModuleCat ℤ} (f : X ⟶ Y) [CategoryTheory.IsIso f] :
    Function.Bijective (fun x => f x) :=
  ⟨(ModuleCat.mono_iff_injective f).mp (IsIso.mono_of_iso f),
    (ModuleCat.epi_iff_surjective f).mp (IsIso.epi_of_iso f)⟩

/-- An isomorphism in `ModuleCat ℤ` is a bijective map (explicit form). -/
theorem bijective_of_isIso' {X Y : ModuleCat ℤ} (f : X ⟶ Y) (h : CategoryTheory.IsIso f) :
    Function.Bijective (fun x => f x) :=
  @bijective_of_isIso X Y f h

/-- Transporting a homology class along an equality of degrees commutes with applying a chain map. -/
lemma cast_homologyMap {C D : ChainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D) {a b : ℕ} (h : a = b)
    (x : C.homology a) :
    (HomologicalComplex.homologyMap φ b) (show C.homology b from h ▸ x)
      = show D.homology b from h ▸ ((HomologicalComplex.homologyMap φ a) x) := by
  subst h; rfl

/-- `imgToInt` and `hInt` are mutually inverse. -/
theorem imgToInt_comp_hInt :
    imgToInt (M := M) ≫ DoubleFC.hInt 8 M
      = 𝟙 (TopCat.of (DoubleFC.intImg 8 M)) := by
  apply CategoryTheory.ConcreteCategory.hom_ext
  intro z
  exact (DoubleFC.eInt 8 M).apply_symm_apply z

theorem hInt_comp_imgToInt :
    DoubleFC.hInt 8 M ≫ imgToInt (M := M)
      = 𝟙 (TopCat.of (DoubleFC.intSet 8 M)) := by
  apply CategoryTheory.ConcreteCategory.hom_ext
  intro z
  exact (DoubleFC.eInt 8 M).symm_apply_apply z

/-- `suppOf K` is contained in the interior when `K` is. -/
theorem suppOf_subset_intSet {K : Set (Double 8 M)} (hKW : K ⊆ DoubleFC.intImg 8 M) :
    suppOf (M := M) K ⊆ DoubleFC.intSet 8 M := by
  intro x hx
  have h1 : x ∈ suppOf (M := M) (DoubleFC.intImg 8 M) := suppOf_mono hKW hx
  rwa [suppOf_intImg] at h1

/-- **A finite cover of a compact subset of `intImg` by coordinate balls inside `intImg`**, with the
distinguished points lying in the interior of `M`. -/
theorem exists_ball_cover_intImg (K : Set (Double 8 M)) (hKc : IsCompact K)
    (hKW : K ⊆ DoubleFC.intImg 8 M) :
    ∃ t : Finset (Set (Double 8 M) × ↥(DoubleFC.intImg 8 M)),
      (∀ p ∈ t, IsCoordBall 9 (TopCat.of (Double 8 M)) p.1) ∧
      (∀ p ∈ t, (p.2 : Double 8 M) ∈ p.1) ∧ K ⊆ ⋃ p ∈ t, p.1 ∧
      (⋃ p ∈ t, p.1) ⊆ DoubleFC.intImg 8 M := by
  classical
  have hdisj : Disjoint K ((DoubleFC.intImg 8 M)ᶜ) :=
    Set.disjoint_left.mpr (fun a ha ha' => ha' (hKW ha))
  obtain ⟨t₀, hLt, hxt, -, hcovK, hdisj2⟩ :=
    Work.ThomBordism.exists_ball_cover_avoiding 9 (by norm_num) (TopCat.of (Double 8 M))
      (A := K) (S := (DoubleFC.intImg 8 M)ᶜ) hKc hdisj (isOpen_intImg (M := M)).isClosed_compl
  have hsub : (⋃ p ∈ t₀, p.1) ⊆ DoubleFC.intImg 8 M := by
    intro a ha
    by_contra ha'
    exact Set.disjoint_left.mp hdisj2 ha' ha
  have hxint : ∀ p ∈ t₀, p.2 ∈ DoubleFC.intImg 8 M :=
    fun p hp => hsub (Set.mem_iUnion₂.mpr ⟨p, hp, hxt p hp⟩)
  let F : {p // p ∈ t₀} → Set (Double 8 M) × ↥(DoubleFC.intImg 8 M) :=
    fun q => (q.1.1, ⟨q.1.2, hxint q.1 q.2⟩)
  refine ⟨t₀.attach.image F, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hp
    exact hLt q.1 q.2
  · intro p hp
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hp
    exact hxt q.1 q.2
  · intro z hz
    obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp (hcovK hz)
    exact Set.mem_iUnion₂.mpr ⟨F ⟨p, hp⟩,
      Finset.mem_image.mpr ⟨⟨p, hp⟩, Finset.mem_attach _ _, rfl⟩, hzp⟩
  · intro z hz
    obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp hz
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hp
    exact hsub (Set.mem_iUnion₂.mpr ⟨q.1, q.2, hzp⟩)

/-! ## The two naturality steps of the cap product -/

/-- `bdryIncl` is the pair map of the identity of `M`. -/
theorem bdryIncl_eq_relChainsMapOf (K : Set M) (hK : K ⊆ (bdry9 M)ᶜ) :
    bdryIncl (M := M) K hK
      = Work.Cohomology.relChainsMapOf (TopCat.of M) (TopCat.of M) (bdry9 M) (Kᶜ)
          (𝟙 (TopCat.of M))
          (Work.Cohomology.relMapSub (bdry9 M) (Kᶜ) (𝟙 (TopCat.of M))
            (fun x hx hxK => hK hxK hx))
          (Work.Cohomology.relMapSub_spec _ _ _ _) := by
  apply (cancel_epi (CategoryTheory.Limits.cokernel.π
    (Work.Cohomology.inclChains (TopCat.of M) (bdry9 M)))).1
  rw [Work.Cohomology.capRel_cokernel_π_relChainsMapOf, Work.Cohomology.chainMap_id',
    Category.id_comp]
  have h : bdryIncl (M := M) K hK
      = Work.Cohomology.relCokerMap (TopCat.of M) (bdry9 M) (Kᶜ)
          (fun x hx hxK => hK hxK hx) := rfl
  rw [h, Work.Cohomology.relCokerMap_comp_π]

/-- **Naturality of the cap product along `∂M ⊆ Kᶜ`.** -/
theorem relCapPair_bdryIncl (K : Set M) (hK : K ⊆ (bdry9 M)ᶜ) (k m : ℕ)
    (u : (Work.Cohomology.relComplex ℤ (TopCat.of M) (Kᶜ)).homology k)
    (w : (Work.Cohomology.relChains (TopCat.of M) (bdry9 M)).homology 9)
    (hkm : k + m = 9) :
    (Work.Cohomology.relCapPair (TopCat.of M) (bdry9 M) k m)
        ((HomologicalComplex.homologyMap (Work.ThomBordism.relRestrOffBdry (M := M) K hK) k) u)
        (show (Work.Cohomology.relChains (TopCat.of M) (bdry9 M)).homology (k + m) from hkm ▸ w)
      = (Work.Cohomology.relCapPair (TopCat.of M) (Kᶜ) k m) u
          (show (Work.Cohomology.relChains (TopCat.of M) (Kᶜ)).homology (k + m) from
            hkm ▸ ((HomologicalComplex.homologyMap (bdryIncl (M := M) K hK) 9) w)) := by
  have h1 := Work.Cohomology.Crux.relCapPair_natural (X₁ := TopCat.of M) (X₂ := TopCat.of M)
    (bdry9 M) (Kᶜ) (𝟙 (TopCat.of M)) (fun x hx hxK => hK hxK hx) k m u
    (show (Work.Cohomology.relChains (TopCat.of M) (bdry9 M)).homology (k + m) from hkm ▸ w)
  rw [Work.Cohomology.chainMap_id', HomologicalComplex.homologyMap_id] at h1
  simp only [ModuleCat.hom_id, LinearMap.id_apply] at h1
  rw [cast_homologyMap _ hkm.symm w] at h1
  rw [← bdryIncl_eq_relChainsMapOf (M := M) K hK] at h1
  exact h1

/-- The unfolding of `relRestrOffBdry` as a `relComplexMap`. -/
theorem relRestrOffBdry_eq (K : Set M) (hK : K ⊆ (bdry9 M)ᶜ) :
    Work.ThomBordism.relRestrOffBdry (M := M) K hK
      = Work.Cohomology.relComplexMap (X₁ := TopCat.of M) (X₂ := TopCat.of M) ℤ
          (bdry9 M) (Kᶜ) (𝟙 (TopCat.of M)) (fun x hx hxK => hK hxK hx) := by
  unfold Work.ThomBordism.relRestrOffBdry
  rfl

/-- **Functoriality of `relComplexMap` under enlarging the excluded set.** -/
theorem relComplexMap_restr_comp (K K' : Set M) (hK : K ⊆ (bdry9 M)ᶜ) (hK' : K' ⊆ (bdry9 M)ᶜ)
    (hKK' : K ⊆ K') :
    Work.Cohomology.relComplexMap (X₁ := TopCat.of M) (X₂ := TopCat.of M) ℤ
        (bdry9 M) (Kᶜ) (𝟙 (TopCat.of M)) (fun x hx hxK => hK hxK hx)
      = Work.Cohomology.relComplexMap (X₁ := TopCat.of M) (X₂ := TopCat.of M) ℤ
            (K'ᶜ) (Kᶜ) (𝟙 (TopCat.of M)) (fun x hx hxK => hx (hKK' hxK))
        ≫ Work.Cohomology.relComplexMap (X₁ := TopCat.of M) (X₂ := TopCat.of M) ℤ
            (bdry9 M) (K'ᶜ) (𝟙 (TopCat.of M)) (fun x hx hxK => hK' hxK hx) :=
  Work.Cohomology.pdmd_relComplexMap_comp (X₀ := TopCat.of M) (X₁ := TopCat.of M)
    (X₂ := TopCat.of M) (bdry9 M) (K'ᶜ) (Kᶜ) (𝟙 (TopCat.of M)) (𝟙 (TopCat.of M))
    (fun x hx hxK => hK' hxK hx) (fun x hx hxK => hx (hKK' hxK))

/-- **Functoriality of `relRestrOffBdry`** under enlarging the compact set. -/
theorem relRestrOffBdry_comp (K K' : Set M) (hK : K ⊆ (bdry9 M)ᶜ) (hK' : K' ⊆ (bdry9 M)ᶜ)
    (hKK' : K ⊆ K') :
    Work.ThomBordism.relRestrOffBdry (M := M) K hK
      = Work.Cohomology.relComplexMap (X₁ := TopCat.of M) (X₂ := TopCat.of M) ℤ
            (K'ᶜ) (Kᶜ) (𝟙 (TopCat.of M)) (fun x hx hxK => hx (hKK' hxK))
        ≫ Work.ThomBordism.relRestrOffBdry (M := M) K' hK' :=
  (relRestrOffBdry_eq (M := M) K hK).trans <|
    (relComplexMap_restr_comp (M := M) K K' hK hK' hKK').trans <|
      congrArg (fun z => Work.Cohomology.relComplexMap (X₁ := TopCat.of M)
          (X₂ := TopCat.of M) ℤ (K'ᶜ) (Kᶜ) (𝟙 (TopCat.of M))
          (fun x hx hxK => hx (hKK' hxK)) ≫ z) (relRestrOffBdry_eq (M := M) K' hK').symm

/-- **The cohomology isomorphism `H^k(M, M∖suppOf K) ≅ H^k(int M, int M ∖ K)`** induced by the
inverse of the open embedding. -/
theorem relComplexMap_imgInv_isIso (K : Set (Double 8 M)) (hKc : IsCompact K)
    (hKW : K ⊆ DoubleFC.intImg 8 M) (k : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relComplexMap (X₁ := TopCat.of (DoubleFC.intImg 8 M))
        (X₂ := TopCat.of M) ℤ (Arel (M := M) K) ((suppOf (M := M) K)ᶜ)
        (imgInv (M := M)) (compWitness (M := M) K)) k) := by
  have hf : ∀ x ∈ Arel (M := M) K, imgToInt (M := M) x ∈ Brel (M := M) K := by
    intro x hx hxK
    exact hx (by rw [← dblIota_imgInv (M := M) x]; exact hxK)
  have hg : ∀ y ∈ Brel (M := M) K,
      Work.Cohomology.subtypeIncl (TopCat.of M) (DoubleFC.intSet 8 M) y
        ∈ ((suppOf (M := M) K)ᶜ) := by
    intro y hy
    exact hy
  have hgit : ∀ y ∈ Brel (M := M) K, DoubleFC.hInt 8 M y ∈ Arel (M := M) K := by
    intro y hy
    have h1 : ((DoubleFC.hInt 8 M y : DoubleFC.intImg 8 M) : Double 8 M) = doubleιM (y : M) :=
      DoubleFC.eInt_apply_coe 8 M y
    change ((DoubleFC.hInt 8 M y : DoubleFC.intImg 8 M) : Double 8 M) ∈ Kᶜ
    rw [h1]
    exact hy
  have hcov : DoubleFC.intSet 8 M ∪ ((suppOf (M := M) K)ᶜ) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    by_cases hx : x ∈ suppOf (M := M) K
    · exact Or.inl (suppOf_subset_intSet (M := M) hKW hx)
    · exact Or.inr hx
  have h1 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relComplexMap (X₁ := TopCat.of (DoubleFC.intSet 8 M))
        (X₂ := TopCat.of M) ℤ (Brel (M := M) K) ((suppOf (M := M) K)ᶜ)
        (Work.Cohomology.subtypeIncl (TopCat.of M) (DoubleFC.intSet 8 M)) hg) k) :=
    Work.Cohomology.capRel_excision_isIso (X := TopCat.of M) (U := DoubleFC.intSet 8 M)
      ((suppOf (M := M) K)ᶜ) (isOpen_intSet (M := M))
      (hKc.isClosed.preimage (continuous_doubleιM (n := 8) (M := M))).isOpen_compl hcov k hg
  have h2 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relComplexMap (X₁ := TopCat.of (DoubleFC.intImg 8 M))
        (X₂ := TopCat.of (DoubleFC.intSet 8 M)) ℤ (Arel (M := M) K) (Brel (M := M) K)
        (imgToInt (M := M)) hf) k) :=
    Work.Cohomology.pdmd_relComplexMap_iso_of_isIso_pairs (X₁ := TopCat.of (DoubleFC.intImg 8 M))
      (X₂ := TopCat.of (DoubleFC.intSet 8 M)) (Arel (M := M) K)
      (Brel (M := M) K) (imgToInt (M := M)) hf (DoubleFC.hInt 8 M)
      hgit (imgToInt_comp_hInt (M := M)) (hInt_comp_imgToInt (M := M)) k
  exact Work.Cohomology.capRel_isIso_relComplexMap_comp (X₀ := TopCat.of (DoubleFC.intImg 8 M))
    (X₁ := TopCat.of (DoubleFC.intSet 8 M)) (X₂ := TopCat.of M) ℤ (Arel (M := M) K)
    (Brel (M := M) K) ((suppOf (M := M) K)ᶜ) (imgToInt (M := M))
    (Work.Cohomology.subtypeIncl (TopCat.of M) (DoubleFC.intSet 8 M)) hf hg k
    (compWitness (M := M) K) h1 h2

/-- The witness for the pair map `(int M, int M∖suppOf L) → (int M, int M∖K'')` when `L ⊆ K''`. -/
abbrev witSub (L K'' : Set (Double 8 M)) (h : L ⊆ K'') :
    ∀ x ∈ Arel (M := M) K'', imgInv (M := M) x ∈ (suppOf (M := M) L)ᶜ :=
  fun x hx hxK => hx (h (by rw [← dblIota_imgInv (M := M) x]; exact hxK))

/-- **The square relating the cohomology isomorphisms of two nested supports.** -/
theorem relComplexMap_imgInv_square (L K'' : Set (Double 8 M)) (hLK : L ⊆ K'') :
    Work.Cohomology.relComplexMap (X₁ := TopCat.of (DoubleFC.intImg 8 M))
        (X₂ := TopCat.of M) ℤ (Arel (M := M) K'') ((suppOf (M := M) L)ᶜ)
        (imgInv (M := M)) (witSub (M := M) L K'' hLK)
      = Work.Cohomology.relComplexMap (X₁ := TopCat.of (DoubleFC.intImg 8 M))
            (X₂ := TopCat.of M) ℤ (Arel (M := M) L) ((suppOf (M := M) L)ᶜ)
            (imgInv (M := M)) (compWitness (M := M) L)
        ≫ Work.Cohomology.relComplexMap (X₁ := TopCat.of (DoubleFC.intImg 8 M))
            (X₂ := TopCat.of (DoubleFC.intImg 8 M)) ℤ (Arel (M := M) K'') (Arel (M := M) L)
            (𝟙 (TopCat.of (DoubleFC.intImg 8 M))) (fun x hx hxL => hx (hLK hxL)) := by
  exact (Work.Cohomology.pdmd_relComplexMap_congr
      (X₁ := TopCat.of (DoubleFC.intImg 8 M)) (X₂ := TopCat.of M) _ _
      (Category.id_comp (imgInv (M := M))).symm _ _).trans
    (Work.Cohomology.pdmd_relComplexMap_comp (X₀ := TopCat.of (DoubleFC.intImg 8 M))
      (X₁ := TopCat.of (DoubleFC.intImg 8 M)) (X₂ := TopCat.of M) (Arel (M := M) K'')
      (Arel (M := M) L) ((suppOf (M := M) L)ᶜ) (𝟙 (TopCat.of (DoubleFC.intImg 8 M)))
      (imgInv (M := M)) (fun x hx hxL => hx (hLK hxL)) (compWitness (M := M) L))

/-- The composite `s₂ ≫ H_{K''}` is the pair map of the inverse embedding into `Arel L`. -/
theorem relComplexMap_imgInv_square₁ (L K'' : Set (Double 8 M)) (hLK : L ⊆ K'') :
    Work.Cohomology.relComplexMap (X₁ := TopCat.of M) (X₂ := TopCat.of M) ℤ
        ((suppOf (M := M) K'')ᶜ) ((suppOf (M := M) L)ᶜ) (𝟙 (TopCat.of M))
        (fun x hx hxL => hx (suppOf_mono (M := M) hLK hxL))
      ≫ Work.Cohomology.relComplexMap (X₁ := TopCat.of (DoubleFC.intImg 8 M))
          (X₂ := TopCat.of M) ℤ (Arel (M := M) K'') ((suppOf (M := M) K'')ᶜ)
          (imgInv (M := M)) (compWitness (M := M) K'')
      = Work.Cohomology.relComplexMap (X₁ := TopCat.of (DoubleFC.intImg 8 M))
          (X₂ := TopCat.of M) ℤ (Arel (M := M) K'') ((suppOf (M := M) L)ᶜ)
          (imgInv (M := M)) (witSub (M := M) L K'' hLK) :=
  (Work.Cohomology.pdmd_relComplexMap_comp (X₀ := TopCat.of (DoubleFC.intImg 8 M))
    (X₁ := TopCat.of M) (X₂ := TopCat.of M) (Arel (M := M) K'')
    ((suppOf (M := M) K'')ᶜ) ((suppOf (M := M) L)ᶜ) (imgInv (M := M))
    (𝟙 (TopCat.of M)) (compWitness (M := M) K'')
    (fun x hx hxL => hx (suppOf_mono (M := M) hLK hxL))).symm

/-- The restriction map `C^*(M, Kᶜ) ⟶ C^*(M, K'ᶜ)` for `K ⊆ K'`. -/
abbrev restrMap (K K' : Set M) (h : K ⊆ K') :
    Work.Cohomology.relComplex ℤ (TopCat.of M) (Kᶜ) ⟶
      Work.Cohomology.relComplex ℤ (TopCat.of M) (K'ᶜ) :=
  Work.Cohomology.relComplexMap (X₁ := TopCat.of M) (X₂ := TopCat.of M) ℤ
    (K'ᶜ) (Kᶜ) (𝟙 (TopCat.of M)) (fun x hx hxK => hx (h hxK))

/-- The map `H^k(M, M∖suppOf L) ⟶ H^k(int M, int M∖L)` of the open embedding. -/
abbrev imgInvMap (L : Set (Double 8 M)) :
    Work.Cohomology.relComplex ℤ (TopCat.of M) ((suppOf (M := M) L)ᶜ) ⟶
      Work.Cohomology.relComplex ℤ (TopCat.of (DoubleFC.intImg 8 M)) (Arel (M := M) L) :=
  Work.Cohomology.relComplexMap (X₁ := TopCat.of (DoubleFC.intImg 8 M)) (X₂ := TopCat.of M) ℤ
    (Arel (M := M) L) ((suppOf (M := M) L)ᶜ) (imgInv (M := M)) (compWitness (M := M) L)

theorem restrMap_comp (K K' K'' : Set M) (hKK' : K ⊆ K') (hK'K'' : K' ⊆ K'') :
    restrMap K K'' (hKK'.trans hK'K'') = restrMap K K' hKK' ≫ restrMap K' K'' hK'K'' :=
  Work.Cohomology.pdmd_relComplexMap_comp (X₀ := TopCat.of M) (X₁ := TopCat.of M)
    (X₂ := TopCat.of M) ((K'')ᶜ) ((K')ᶜ) ((K)ᶜ) (𝟙 (TopCat.of M)) (𝟙 (TopCat.of M))
    (fun x hx hxK => hx (hK'K'' hxK)) (fun x hx hxK => hx (hKK' hxK))

lemma homologyMap_congr {C D : ChainComplex (ModuleCat ℤ) ℕ} (φ ψ : C ⟶ D) (h : φ = ψ) (n : ℕ) :
    HomologicalComplex.homologyMap φ n = HomologicalComplex.homologyMap ψ n :=
  congrArg (fun θ => HomologicalComplex.homologyMap θ n) h

/-- Functoriality of `relRestrOffBdry` under enlarging the compact set, at the level of classes. -/
theorem relRestrOffBdry_chain (K K' : Set M) (hK : K ⊆ (bdry9 M)ᶜ) (hK' : K' ⊆ (bdry9 M)ᶜ)
    (hKK' : K ⊆ K') (k : ℕ)
    (uK : (Work.Cohomology.relComplex ℤ (TopCat.of M) (Kᶜ)).homology k) :
    (HomologicalComplex.homologyMap (Work.ThomBordism.relRestrOffBdry (M := M) K hK) k) uK
      = (HomologicalComplex.homologyMap (Work.ThomBordism.relRestrOffBdry (M := M) K' hK') k)
          ((HomologicalComplex.homologyMap (restrMap K K' hKK') k) uK) := by
  have h1 : (HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap
        (X₁ := TopCat.of M) (X₂ := TopCat.of M) ℤ (bdry9 M) (Kᶜ) (𝟙 (TopCat.of M))
        (fun x hx hxK => hK hxK hx)) k) uK
      = (HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap
        (X₁ := TopCat.of M) (X₂ := TopCat.of M) ℤ (bdry9 M) (K'ᶜ) (𝟙 (TopCat.of M))
        (fun x hx hxK => hK' hxK hx)) k)
        ((HomologicalComplex.homologyMap (restrMap K K' hKK') k) uK) := by
    rw [relComplexMap_restr_comp (M := M) K K' hK hK' hKK', HomologicalComplex.homologyMap_comp]
    rfl
  have h0 : (HomologicalComplex.homologyMap (Work.ThomBordism.relRestrOffBdry (M := M) K hK) k) uK
      = (HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap
          (X₁ := TopCat.of M) (X₂ := TopCat.of M) ℤ (bdry9 M) (Kᶜ) (𝟙 (TopCat.of M))
          (fun x hx hxK => hK hxK hx)) k) uK :=
    congrArg (fun θ => (ConcreteCategory.hom (HomologicalComplex.homologyMap θ k)) uK)
      (relRestrOffBdry_eq (M := M) K hK)
  have h2 : (HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap
          (X₁ := TopCat.of M) (X₂ := TopCat.of M) ℤ (bdry9 M) (K'ᶜ) (𝟙 (TopCat.of M))
          (fun x hx hxK => hK' hxK hx)) k)
        ((HomologicalComplex.homologyMap (restrMap K K' hKK') k) uK)
      = (HomologicalComplex.homologyMap (Work.ThomBordism.relRestrOffBdry (M := M) K' hK') k)
        ((HomologicalComplex.homologyMap (restrMap K K' hKK') k) uK) :=
    congrArg (fun θ => (ConcreteCategory.hom (HomologicalComplex.homologyMap θ k))
      ((HomologicalComplex.homologyMap (restrMap K K' hKK') k) uK))
      (relRestrOffBdry_eq (M := M) K' hK').symm
  exact h0.trans (h1.trans h2)

/-- **The key computation**: the cap product with `w` on `(M, ∂M)` along a relative class sitting
on the interior of `M` equals the pushforward (along the inverse of the open embedding) of the cap
product with the local fundamental class of `cD`. -/
theorem cap_eq_fpush {β : Type} (w : (Work.Cohomology.relChains (TopCat.of M) (bdry9 M)).homology 9)
    (cD : (Work.Cohomology.singularChains ℤ (TopCat.of (Double 8 M))).homology 9)
    (hcomp : CompHyp (M := M) w cD)
    (s : Finset β) (B : β → Set (Double 8 M)) (y : β → M)
    (hball : ∀ b ∈ s, IsCoordBall 9 (TopCat.of (Double 8 M)) (B b))
    (hx : ∀ b ∈ s, doubleιM (y b) ∈ B b)
    (hsub : (⋃ b ∈ s, B b) ⊆ DoubleFC.intImg 8 M)
    (hLc : IsCompact (⋃ b ∈ s, B b)) (k m : ℕ) (hkm : k + m = 9)
    (uL : (Work.Cohomology.relComplex ℤ (TopCat.of M) ((suppOf (M := M) (⋃ b ∈ s, B b))ᶜ)).homology k)
    (hK : suppOf (M := M) (⋃ b ∈ s, B b) ⊆ (bdry9 M)ᶜ) :
    (Work.Cohomology.relCapPair (TopCat.of M) (bdry9 M) k m)
        ((HomologicalComplex.homologyMap (Work.ThomBordism.relRestrOffBdry (M := M)
          (suppOf (M := M) (⋃ b ∈ s, B b)) hK) k) uL)
        (show (Work.Cohomology.relChains (TopCat.of M) (bdry9 M)).homology (k + m) from hkm ▸ w)
      = (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
            (TopCat.of (DoubleFC.intImg 8 M)) (TopCat.of M) (imgInv (M := M))) m)
          ((Work.Cohomology.relCapPair (TopCat.of (DoubleFC.intImg 8 M))
              (Arel (M := M) (⋃ b ∈ s, B b)) k m)
            ((HomologicalComplex.homologyMap (imgInvMap (M := M) (⋃ b ∈ s, B b)) k) uL)
            (show (Work.Cohomology.relChains (TopCat.of (DoubleFC.intImg 8 M))
                (Arel (M := M) (⋃ b ∈ s, B b))).homology (k + m) from
              hkm ▸ (Work.Cohomology.localFundClass 9 cD (DoubleFC.intImg 8 M)
                (isOpen_intImg (M := M)) (⋃ b ∈ s, B b) hsub hLc))) := by
  rw [relCapPair_bdryIncl (M := M) (suppOf (M := M) (⋃ b ∈ s, B b)) hK k m uL w hkm]
  have hβ := hcomp s B y hball hx hsub
  have hβc : (show (Work.Cohomology.relChains (TopCat.of M)
        ((suppOf (M := M) (⋃ b ∈ s, B b))ᶜ)).homology (k + m) from
        hkm ▸ ((HomologicalComplex.homologyMap (bdryIncl (M := M)
          (suppOf (M := M) (⋃ b ∈ s, B b)) hK) 9) w))
      = (HomologicalComplex.homologyMap (imgPairMap (M := M) (⋃ b ∈ s, B b)
          (suppOf (M := M) (⋃ b ∈ s, B b)) (compWitness (M := M) (⋃ b ∈ s, B b))) (k + m))
          (show (Work.Cohomology.relChains (TopCat.of (DoubleFC.intImg 8 M))
            (Arel (M := M) (⋃ b ∈ s, B b))).homology (k + m) from
            hkm ▸ (Work.Cohomology.localFundClass 9 cD (DoubleFC.intImg 8 M)
              (isOpen_intImg (M := M)) (⋃ b ∈ s, B b) hsub hLc)) := by
    exact ((congrArg (fun z => (show (Work.Cohomology.relChains (TopCat.of M)
        ((suppOf (M := M) (⋃ b ∈ s, B b))ᶜ)).homology (k + m) from hkm ▸ z)) hβ).symm).trans
      (cast_homologyMap (imgPairMap (M := M) (⋃ b ∈ s, B b)
        (suppOf (M := M) (⋃ b ∈ s, B b)) (compWitness (M := M) (⋃ b ∈ s, B b))) hkm.symm
        (Work.Cohomology.localFundClass 9 cD (DoubleFC.intImg 8 M) (isOpen_intImg (M := M))
          (⋃ b ∈ s, B b) hsub hLc)).symm
  rw [hβc, ← Work.Cohomology.Crux.relCapPair_natural
    (X₁ := TopCat.of (DoubleFC.intImg 8 M)) (X₂ := TopCat.of M)
    (Arel (M := M) (⋃ b ∈ s, B b)) ((suppOf (M := M) (⋃ b ∈ s, B b))ᶜ) (imgInv (M := M))
    (compWitness (M := M) (⋃ b ∈ s, B b)) k m uL
    (show (Work.Cohomology.relChains (TopCat.of (DoubleFC.intImg 8 M))
      (Arel (M := M) (⋃ b ∈ s, B b))).homology (k + m) from
      hkm ▸ (Work.Cohomology.localFundClass 9 cD (DoubleFC.intImg 8 M)
        (isOpen_intImg (M := M)) (⋃ b ∈ s, B b) hsub hLc))]

/-- **Middle-degree Lefschetz duality for `(M, ∂M)` from the four pieces.** -/
theorem lefschetzDuality_of_comp
    (w : (Work.Cohomology.relChains (TopCat.of M) (bdry9 M)).homology 9)
    (cD : (Work.Cohomology.singularChains ℤ (TopCat.of (Double 8 M))).homology 9)
    (hgood : Work.Cohomology.Good 9 cD (DoubleFC.intImg 8 M) (isOpen_intImg (M := M)))
    (hcomp : CompHyp (M := M) w cD)
    (P1 : ∀ m : ℕ, Function.Bijective (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of {x : M | x ∉ bdry9 M}) (TopCat.of M)
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)) m))
    (P2 : ∀ k : ℕ, ∀ u : (Work.Cohomology.relComplex ℤ (TopCat.of M) (bdry9 M)).homology k,
      ∃ (K : Set M) (hK : K ⊆ (bdry9 M)ᶜ), IsCompact K ∧
        ∃ x : (Work.Cohomology.relComplex ℤ (TopCat.of M) (Kᶜ)).homology k,
          (HomologicalComplex.homologyMap (Work.ThomBordism.relRestrOffBdry (M := M) K hK) k) x = u) :
    ∀ k m (h : k + m = 9), Function.Bijective (fun z =>
      (Work.Cohomology.relCapPair (TopCat.of M) (bdry9 M) k m) z (h ▸ w)) := by
  intro k m hkm
  have hsplit : (Work.Cohomology.chainMap ℤ (TopCat.of (DoubleFC.intImg 8 M)) (TopCat.of M)
      (imgInv (M := M)))
      = Work.Cohomology.chainMap ℤ (TopCat.of (DoubleFC.intImg 8 M))
          (TopCat.of (DoubleFC.intSet 8 M)) (imgToInt (M := M))
        ≫ Work.Cohomology.chainMap ℤ (TopCat.of (DoubleFC.intSet 8 M)) (TopCat.of M)
            (Work.Cohomology.subtypeIncl (TopCat.of M) (DoubleFC.intSet 8 M)) :=
    Work.Cohomology.chainMap_comp_relChains ℤ (imgToInt (M := M))
      (Work.Cohomology.subtypeIncl (TopCat.of M) (DoubleFC.intSet 8 M))
  have hbij : Function.Bijective (fun z => (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (DoubleFC.intImg 8 M)) (TopCat.of M)
        (imgInv (M := M))) m) z) := by
    have h1 : Function.Bijective (fun z => (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of (DoubleFC.intSet 8 M)) (TopCat.of M)
          (Work.Cohomology.subtypeIncl (TopCat.of M) (DoubleFC.intSet 8 M))) m) z) := P1 m
    have h2 : Function.Bijective (fun z => (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of (DoubleFC.intImg 8 M))
          (TopCat.of (DoubleFC.intSet 8 M)) (imgToInt (M := M))) m) z) := by
      rw [imgToInt_eq (M := M)]
      exact bijective_of_isIso' _
        (Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv
          (X := TopCat.of (DoubleFC.intImg 8 M)) (Y := TopCat.of (DoubleFC.intSet 8 M))
          (DoubleFC.eInt 8 M).symm.toHomotopyEquiv m)
    rw [congrArg (fun φ => HomologicalComplex.homologyMap φ m) hsplit,
      HomologicalComplex.homologyMap_comp]
    change Function.Bijective (fun z => (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (DoubleFC.intSet 8 M)) (TopCat.of M)
        (Work.Cohomology.subtypeIncl (TopCat.of M) (DoubleFC.intSet 8 M))) m)
      ((HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
        (TopCat.of (DoubleFC.intImg 8 M)) (TopCat.of (DoubleFC.intSet 8 M))
        (imgToInt (M := M))) m) z))
    exact h1.comp h2
  refine ⟨?_, ?_⟩
  · intro u1 u2 huv
    have hzero : ∀ u : (Work.Cohomology.relComplex ℤ (TopCat.of M) (bdry9 M)).homology k,
        (Work.Cohomology.relCapPair (TopCat.of M) (bdry9 M) k m) u (hkm ▸ w) = 0 → u = 0 := by
      intro u hu
      obtain ⟨K, hK, hKc, uK, huK⟩ := P2 k u
      have hKimg : IsCompact (doubleιM (n := 8) (M := M) '' K) :=
        hKc.image (continuous_doubleιM (n := 8) (M := M))
      have hKimg_sub : doubleιM (n := 8) (M := M) '' K ⊆ DoubleFC.intImg 8 M := by
        rintro z ⟨x, hx, rfl⟩
        exact (show x ∈ suppOf (M := M) (DoubleFC.intImg 8 M) from by
          rw [suppOf_intImg (M := M)]; exact hK hx)
      obtain ⟨t, hLt, hxt, hcovK, hsubL⟩ := exists_ball_cover_intImg (M := M) _ hKimg hKimg_sub
      have hxL : ∀ p ∈ t, doubleιM (n := 8) (M := M) (imgInv (M := M) p.2) ∈ p.1 :=
        fun p hp => by rw [dblIota_imgInv (M := M) p.2]; exact hxt p hp
      have hLc : IsCompact (⋃ p ∈ t, p.1) :=
        t.isCompact_biUnion (fun p hp => (hLt p hp).isCompact)
      have hK' : suppOf (M := M) (⋃ p ∈ t, p.1) ⊆ (bdry9 M)ᶜ :=
        suppOf_subset_intSet (M := M) hsubL
      have hKK' : K ⊆ suppOf (M := M) (⋃ p ∈ t, p.1) := fun x hx => hcovK ⟨x, hx, rfl⟩
      -- u as the image of uK under the restriction to `suppOf L`
      have huK' : u = (HomologicalComplex.homologyMap
          (Work.ThomBordism.relRestrOffBdry (M := M) (suppOf (M := M) (⋃ p ∈ t, p.1)) hK') k)
          ((HomologicalComplex.homologyMap (restrMap K (suppOf (M := M) (⋃ p ∈ t, p.1)) hKK') k)
            uK) :=
        huK.symm.trans (relRestrOffBdry_chain (M := M) K _ hK hK' hKK' k uK)
      have h0' : (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
            (TopCat.of (DoubleFC.intImg 8 M)) (TopCat.of M) (imgInv (M := M))) m)
          ((Work.Cohomology.relCapPair (TopCat.of (DoubleFC.intImg 8 M))
            (Arel (M := M) (⋃ p ∈ t, p.1)) k m)
            ((HomologicalComplex.homologyMap (imgInvMap (M := M) (⋃ p ∈ t, p.1)) k)
              ((HomologicalComplex.homologyMap
                (restrMap K (suppOf (M := M) (⋃ p ∈ t, p.1)) hKK') k) uK))
            (show (Work.Cohomology.relChains (TopCat.of (DoubleFC.intImg 8 M))
                (Arel (M := M) (⋃ p ∈ t, p.1))).homology (k + m) from
              hkm ▸ (Work.Cohomology.localFundClass 9 cD (DoubleFC.intImg 8 M)
                (isOpen_intImg (M := M)) (⋃ p ∈ t, p.1) hsubL hLc))) = 0 :=
        (cap_eq_fpush (M := M) w cD hcomp t (fun p => p.1) (fun p => imgInv (M := M) p.2)
            hLt hxL hsubL hLc k m hkm _ hK').symm.trans (huK' ▸ hu)
      -- injectivity of `f_*` kills the `H_m(int M)` class
      have hx0 : Work.Cohomology.goodD 9 cD (DoubleFC.intImg 8 M) (isOpen_intImg (M := M))
          (⋃ p ∈ t, p.1) hsubL hLc k m hkm
          ((HomologicalComplex.homologyMap (imgInvMap (M := M) (⋃ p ∈ t, p.1)) k)
            ((HomologicalComplex.homologyMap
              (restrMap K (suppOf (M := M) (⋃ p ∈ t, p.1)) hKK') k) uK)) = 0 :=
        hbij.1 (h0'.trans (map_zero _).symm)
      obtain ⟨K'', hLKK'', hK''W, hK''c, hkill⟩ :=
        Work.Cohomology.Good.kill hgood k m hkm (⋃ p ∈ t, p.1) hsubL hLc
          ((HomologicalComplex.homologyMap (imgInvMap (M := M) (⋃ p ∈ t, p.1)) k)
            ((HomologicalComplex.homologyMap
              (restrMap K (suppOf (M := M) (⋃ p ∈ t, p.1)) hKK') k) uK)) hx0
      have hK''sub : suppOf (M := M) K'' ⊆ (bdry9 M)ᶜ := suppOf_subset_intSet (M := M) hK''W
      have hle : (⋃ p ∈ t, p.1) ⊆ K'' := hLKK''
      -- the class `uK'` is killed in `H^k(M, (suppOf K'')ᶜ)`
      have hs2 : (HomologicalComplex.homologyMap
            (restrMap (suppOf (M := M) (⋃ p ∈ t, p.1)) (suppOf (M := M) K'')
              (suppOf_mono (M := M) hle)) k)
          ((HomologicalComplex.homologyMap
            (restrMap K (suppOf (M := M) (⋃ p ∈ t, p.1)) hKK') k) uK) = 0 := by
        apply (bijective_of_isIso' _ (relComplexMap_imgInv_isIso (M := M) K'' hK''c hK''W k)).1
        have hsq := congrArg (fun θ => (ConcreteCategory.hom (HomologicalComplex.homologyMap θ k))
            ((HomologicalComplex.homologyMap
              (restrMap K (suppOf (M := M) (⋃ p ∈ t, p.1)) hKK') k) uK))
          ((relComplexMap_imgInv_square₁ (M := M) (⋃ p ∈ t, p.1) K'' hle).trans
            (relComplexMap_imgInv_square (M := M) (⋃ p ∈ t, p.1) K'' hle))
        simp only [HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp,
          LinearMap.comp_apply] at hsq
        exact (hsq.trans hkill).trans (map_zero _).symm
      -- hence `u = 0`
      have h1 : u = (HomologicalComplex.homologyMap
          (Work.ThomBordism.relRestrOffBdry (M := M) (suppOf (M := M) K'') hK''sub) k)
          ((HomologicalComplex.homologyMap
            (restrMap K (suppOf (M := M) K'') (hKK'.trans (suppOf_mono (M := M) hle))) k) uK) :=
        huK.symm.trans (relRestrOffBdry_chain (M := M) K _ hK hK''sub
          (hKK'.trans (suppOf_mono (M := M) hle)) k uK)
      have h2 : (HomologicalComplex.homologyMap
            (restrMap K (suppOf (M := M) K'') (hKK'.trans (suppOf_mono (M := M) hle))) k) uK
          = (HomologicalComplex.homologyMap
            (restrMap (suppOf (M := M) (⋃ p ∈ t, p.1)) (suppOf (M := M) K'')
              (suppOf_mono (M := M) hle)) k)
            ((HomologicalComplex.homologyMap
              (restrMap K (suppOf (M := M) (⋃ p ∈ t, p.1)) hKK') k) uK) := by
        rw [restrMap_comp (M := M) K _ _ hKK' (suppOf_mono (M := M) hle),
          HomologicalComplex.homologyMap_comp]
        rfl
      rw [h1, h2, hs2]
      simp only [map_zero]
    have hzero2 : (Work.Cohomology.relCapPair (TopCat.of M) (bdry9 M) k m) (u1 - u2) (hkm ▸ w) = 0 := by
      rw [map_sub, LinearMap.sub_apply]
      exact sub_eq_zero.mpr huv
    exact sub_eq_zero.mp (hzero (u1 - u2) hzero2)
  · intro y
    obtain ⟨y', hy'⟩ := hbij.2 y
    obtain ⟨K, hKU, hKc, x, hx⟩ := Work.Cohomology.Good.hit hgood k m hkm y'
    obtain ⟨t, hLt, hxt, hcovK, hsubL⟩ := exists_ball_cover_intImg (M := M) K hKc hKU
    have hxL : ∀ p ∈ t, doubleιM (n := 8) (M := M) (imgInv (M := M) p.2) ∈ p.1 :=
      fun p hp => by rw [dblIota_imgInv (M := M) p.2]; exact hxt p hp
    have hLc : IsCompact (⋃ p ∈ t, p.1) :=
      t.isCompact_biUnion (fun p hp => (hLt p hp).isCompact)
    have hK' : suppOf (M := M) (⋃ p ∈ t, p.1) ⊆ (bdry9 M)ᶜ :=
      suppOf_subset_intSet (M := M) hsubL
    have hx' : (Work.Cohomology.goodD 9 cD (DoubleFC.intImg 8 M) (isOpen_intImg (M := M))
        (⋃ p ∈ t, p.1) hsubL hLc k m hkm
        ((HomologicalComplex.homologyMap
          (Work.Cohomology.pdRelComplexEnlarge (DoubleFC.intImg 8 M) hcovK) k) x)) = y' := by
      rw [Work.Cohomology.pd_goodD_natural (M := TopCat.of (Double 8 M)) 9 cD
        (DoubleFC.intImg 8 M) (isOpen_intImg (M := M)) hcovK hKU hsubL hKc hLc k m hkm x]
      exact hx
    obtain ⟨uL, huL⟩ : ∃ uL : (Work.Cohomology.relComplex ℤ (TopCat.of M)
        ((suppOf (M := M) (⋃ p ∈ t, p.1))ᶜ)).homology k,
        (HomologicalComplex.homologyMap (imgInvMap (M := M) (⋃ p ∈ t, p.1)) k) uL
          = (HomologicalComplex.homologyMap
              (Work.Cohomology.pdRelComplexEnlarge (DoubleFC.intImg 8 M) hcovK) k) x :=
      (bijective_of_isIso' _ (relComplexMap_imgInv_isIso (M := M) (⋃ p ∈ t, p.1) hLc hsubL k)).2
        ((HomologicalComplex.homologyMap
          (Work.Cohomology.pdRelComplexEnlarge (DoubleFC.intImg 8 M) hcovK) k) x)
    refine ⟨(HomologicalComplex.homologyMap (Work.ThomBordism.relRestrOffBdry
      (M := M) (suppOf (M := M) (⋃ p ∈ t, p.1)) hK') k) uL, ?_⟩
    refine (cap_eq_fpush (M := M) w cD hcomp t (fun p => p.1) (fun p => imgInv (M := M) p.2)
      hLt hxL hsubL hLc k m hkm uL hK').trans ?_
    rw [huL]
    have hsteps : (Work.Cohomology.relCapPair (TopCat.of (DoubleFC.intImg 8 M))
          (Arel (M := M) (⋃ p ∈ t, p.1)) k m)
        ((HomologicalComplex.homologyMap
          (Work.Cohomology.pdRelComplexEnlarge (DoubleFC.intImg 8 M) hcovK) k) x)
        (show (Work.Cohomology.relChains (TopCat.of (DoubleFC.intImg 8 M))
            (Arel (M := M) (⋃ p ∈ t, p.1))).homology (k + m) from
          hkm ▸ (Work.Cohomology.localFundClass 9 cD (DoubleFC.intImg 8 M)
            (isOpen_intImg (M := M)) (⋃ p ∈ t, p.1) hsubL hLc)) = y' := by
      exact (by rfl : (Work.Cohomology.relCapPair (TopCat.of (DoubleFC.intImg 8 M))
          (Arel (M := M) (⋃ p ∈ t, p.1)) k m)
        ((HomologicalComplex.homologyMap
          (Work.Cohomology.pdRelComplexEnlarge (DoubleFC.intImg 8 M) hcovK) k) x)
        (show (Work.Cohomology.relChains (TopCat.of (DoubleFC.intImg 8 M))
            (Arel (M := M) (⋃ p ∈ t, p.1))).homology (k + m) from
          hkm ▸ (Work.Cohomology.localFundClass 9 cD (DoubleFC.intImg 8 M)
            (isOpen_intImg (M := M)) (⋃ p ∈ t, p.1) hsubL hLc))
        = Work.Cohomology.goodD 9 cD (DoubleFC.intImg 8 M) (isOpen_intImg (M := M))
            (⋃ p ∈ t, p.1) hsubL hLc k m hkm
            ((HomologicalComplex.homologyMap
              (Work.Cohomology.pdRelComplexEnlarge (DoubleFC.intImg 8 M) hcovK) k) x)).trans hx'
    exact (congrArg (fun z => (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
        (TopCat.of (DoubleFC.intImg 8 M)) (TopCat.of M) (imgInv (M := M))) m) z) hsteps).trans hy'



/-- **The fundamental class of the double, its local classes and `Good` for the interior.**

This packages `Work.ThomBordism.RelDoubleClass.relDoubleClass_exists` with the local-generation
argument of `Work.ThomBordism.RelDoubleClass.doubleFundClass` and the hypothesis `P3`. -/
theorem doubleClassPieces
    (w : (Work.Cohomology.relChains (TopCat.of M) (bdry9 M)).homology 9)
    (hw : ∀ (x : M) (hx : x ∉ bdry9 M),
      Submodule.span ℤ {(HomologicalComplex.homologyMap
        (Work.ThomBordism.relChainsInclPunct (TopCat.of M) (bdry9 M) x hx) 9 w)} = ⊤)
    (P3 : ∀ {N : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin N)) (Work.ThomBordism.Double 8 M)]
      (c : (Work.Cohomology.singularChains ℤ (TopCat.of (Work.ThomBordism.Double 8 M))).homology N)
      (hc : ∀ x : Work.ThomBordism.Double 8 M, Submodule.span ℤ {(HomologicalComplex.homologyMap
        (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
          (TopCat.of (Work.ThomBordism.Double 8 M)) {y | y ≠ x})) N c)} = ⊤)
      (hN : 1 ≤ N), ∀ (U : Set (Work.ThomBordism.Double 8 M)) (hU : IsOpen U),
        Work.Cohomology.Good N c U hU) :
    ∃ cD : (Work.Cohomology.singularChains ℤ (TopCat.of (Work.ThomBordism.Double 8 M))).homology 9,
      (∀ x : Work.ThomBordism.Double 8 M, Submodule.span ℤ {(HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsProj (TopCat.of (Work.ThomBordism.Double 8 M)) {y | y ≠ x})
          9 cD)} = ⊤) ∧
      (∀ (y : M) (hy : y ∉ bdry9 M),
        Work.ThomBordism.localClassAt (TopCat.of (Work.ThomBordism.Double 8 M)) 9 cD
          (Work.ThomBordism.doubleιM (n := 8) (M := M) y)
        = (HomologicalComplex.homologyMap (Work.ThomBordism.DoubleFC.pairMapιM 8 M y) 9)
            (Work.ThomBordism.RelDoubleClass.locW (n := 8) (M := M) w y hy)) ∧
      Work.Cohomology.Good 9 cD (DoubleFC.intImg 8 M) (isOpen_intImg (M := M)) := by
  obtain ⟨cD, hMcls, hNcls, -⟩ :=
    Work.ThomBordism.RelDoubleClass.relDoubleClass_exists (n := 8) (M := M) w
  have hgenM : ∀ (y : M) (hy : y ∉ bdry9 M),
      Submodule.span ℤ {(Work.ThomBordism.localClassAt
        (TopCat.of (Work.ThomBordism.Double 8 M)) 9 cD
        (Work.ThomBordism.doubleιM (n := 8) (M := M) y))} = ⊤ := by
    intro y hy
    rw [hMcls y hy]
    exact Work.ThomBordism.doubleFC.span_pairMap_M 8 M y hy
      (Work.ThomBordism.RelDoubleClass.locW (n := 8) (M := M) w y hy) (hw y hy)
  have hgenN : ∀ (y : M) (hy : y ∉ bdry9 M),
      Submodule.span ℤ {(Work.ThomBordism.localClassAt
        (TopCat.of (Work.ThomBordism.Double 8 M)) 9 cD
        (Work.ThomBordism.doubleιN (n := 8) (M := M) y))} = ⊤ := by
    intro y hy
    have h := Work.ThomBordism.doubleFC.span_pairMap_N 8 M y hy
      (Work.ThomBordism.RelDoubleClass.locW (n := 8) (M := M) w y hy) (hw y hy)
    set v := (HomologicalComplex.homologyMap (DoubleFC.pairMapιN 8 M y) 9)
      (Work.ThomBordism.RelDoubleClass.locW (n := 8) (M := M) w y hy) with hv
    have hneg : Submodule.span ℤ ({(-v)} : Set _) = ⊤ := by
      rw [show ({(-v)} : Set _) = -({v} : Set _) from (Set.neg_singleton v).symm,
        Submodule.span_neg]
      exact h
    rw [hNcls y hy, ← hv]
    exact hneg
  have hgen : ∀ x : Work.ThomBordism.Double 8 M, Submodule.span ℤ {(HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsProj (TopCat.of (Work.ThomBordism.Double 8 M)) {y | y ≠ x})
        9 cD)} = ⊤ := by
    intro x
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    rcases a with m | m
    · by_cases hb : m ∈ bdry9 M
      · exact DoubleFC.span_localClassAt_seam 8 M cD hgenM ⟨m, hb⟩
      · exact hgenM m hb
    · by_cases hb : m ∈ bdry9 M
      · exact DoubleFC.span_localClassAt_seamN 8 M cD hgenM ⟨m, hb⟩
      · exact hgenN m hb
  refine ⟨cD, hgen, hMcls, ?_⟩
  exact P3 cD (fun x => hgen x) (by norm_num) (DoubleFC.intImg 8 M) (isOpen_intImg (M := M))

end

end Work.ThomBordism.RelDuality

import Mathlib
import Submission.Work.Tubular.tubeHalfOrientation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open scoped Topology
open CategoryTheory CategoryTheory.Limits

namespace Work.Tubular

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k] {ε : ℝ}

/-! ## Generic comparison lemmas for relative chain complexes -/

/-- The composite `cokernel.π ≫ relChainsMapOf` is the chain map followed by `cokernel.π`. -/
theorem cokernel_π_relChainsMapOf_tub {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B) :
    cokernel.π (Work.Cohomology.inclChains X A) ≫ Work.Cohomology.relChainsMapOf X Y A B f g w
      = Work.Cohomology.chainMap ℤ X Y f ≫ cokernel.π (Work.Cohomology.inclChains Y B) := by
  rw [Work.Cohomology.relChainsMapOf]
  exact Work.Cohomology.cokernel_π_map (Work.Cohomology.inclChains X A)
    (Work.Cohomology.inclChains Y B) (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) g)
    (Work.Cohomology.chainMap ℤ X Y f) _

/-- Naturality of `relChainsMapOf` in the relative subsets: enlarging the relative sets commutes with
the maps of pairs. -/
theorem relChainsMapOf_relCokerMap_tub {X Y : TopCat} {A A' : Set X} (hA : A' ⊆ A)
    {B B' : Set Y} (hB : B' ⊆ B) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B)
    (g' : TopCat.of A' ⟶ TopCat.of B')
    (w' : Work.Cohomology.subtypeIncl X A' ≫ f = g' ≫ Work.Cohomology.subtypeIncl Y B') :
    Work.Cohomology.relChainsMapOf X Y A' B' f g' w' ≫ Work.Cohomology.relCokerMap Y B' B hB
      = Work.Cohomology.relCokerMap X A' A hA
        ≫ Work.Cohomology.relChainsMapOf X Y A B f g w := by
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains X A'))).1
  rw [← Category.assoc, cokernel_π_relChainsMapOf_tub A' B' f g' w', Category.assoc,
    Work.Cohomology.relCokerMap_comp_π, ← Category.assoc,
    Work.Cohomology.relCokerMap_comp_π, cokernel_π_relChainsMapOf_tub A B f g w]

/-- `relChainsMapOf` depends on the two maps only through their values. -/
theorem relChainsMapOf_congr_tub {X Y : TopCat} (A : Set X) (B : Set Y)
    {f f' : X ⟶ Y} (hf : f = f') {g g' : TopCat.of A ⟶ TopCat.of B} (hg : g = g')
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B)
    (w' : Work.Cohomology.subtypeIncl X A ≫ f' = g' ≫ Work.Cohomology.subtypeIncl Y B) :
    Work.Cohomology.relChainsMapOf X Y A B f g w = Work.Cohomology.relChainsMapOf X Y A B f' g' w' := by
  subst hf; subst hg; rfl

/-! ## The tubular maps of pairs, as `TopCat` morphisms -/

/-- The inverse of the tubular map, as a morphism from the open tube to the disc bundle. -/
noncomputable def invOpenTubeTop {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (C : TubeChart E ε) :
    TopCat.of ↥(openTubeSet E ε) ⟶ TopCat.of (NormalDiscSub E ε) :=
  TopCat.ofHom (invOpenTube C)

/-- The restriction of the inverse tubular map to the relative complements. -/
noncomputable def invSubTop {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (C : TubeChart E ε) (K : Set (NormalDiscSub E ε)) :
    TopCat.of ↥(tubeRelSub (E := E) K) ⟶ TopCat.of ↥(discRelSub (E := E) K) :=
  TopCat.ofHom ⟨fun y => ⟨invOpenTube C y.1, inv_mem_discRelSub C y.2⟩,
      Continuous.subtype_mk ((invOpenTube C).continuous.comp continuous_subtype_val)
        (fun y => inv_mem_discRelSub C y.2)⟩

/-- The tubular map, as a morphism from the disc bundle to the ambient space. -/
noncomputable def tubeMapTop {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} :
    TopCat.of (NormalDiscSub E ε) ⟶ TopCat.of (Euc (8 + k)) :=
  TopCat.ofHom ⟨fun q => tubeMap E (q : NormalTotal E),
    (continuous_tubeMap E).comp continuous_subtype_val⟩

/-- The restriction of the tubular map to the relative complements. -/
noncomputable def tubeSubTop {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (C : TubeChart E ε) (K : Set (NormalDiscSub E ε)) :
    TopCat.of ↥(discRelSub (E := E) K) ⟶ TopCat.of ↥((tubeImage (E := E) K)ᶜ) :=
  TopCat.ofHom ⟨fun q => ⟨tubeMap E (q.1 : NormalTotal E), by
        intro hmem
        obtain ⟨q', hq', hq'e⟩ := mem_tubeImage.mp hmem
        exact q.2 ((tubeMap_injective C hq'e) ▸ hq')⟩,
      Continuous.subtype_mk ((continuous_tubeMap E).comp
        (continuous_subtype_val.comp continuous_subtype_val)) (fun q => by
        intro hmem
        obtain ⟨q', hq', hq'e⟩ := mem_tubeImage.mp hmem
        exact q.2 ((tubeMap_injective C hq'e) ▸ hq'))⟩

/-- The composite of the two tubular maps is the inclusion. -/
theorem invOpenTubeTop_comp_tubeMapTop {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (C : TubeChart E ε) :
    invOpenTubeTop C ≫ tubeMapTop (E := E)
      = Work.Cohomology.subtypeIncl (TopCat.of (Euc (8 + k))) (openTubeSet E ε) := by
  apply TopCat.ext
  intro y
  show tubeMap E ((invOpenTube C) y : NormalTotal E) = y
  exact tubeMap_invOpenTube C y

/-- The composite of the two relative restrictions is the inclusion. -/
theorem invSubTop_comp_tubeSubTop {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (C : TubeChart E ε) (K : Set (NormalDiscSub E ε)) :
    invSubTop C K ≫ tubeSubTop C K
      = Work.Cohomology.inclInterA (TopCat.of (Euc (8 + k)))
        (openTubeSet E ε) (tubeImage (E := E) K)ᶜ := by
  apply TopCat.ext
  intro y
  simp only [TopCat.hom_ofHom, Work.Cohomology.inclInterA, ContinuousMap.coe_mk]
  exact Subtype.ext (tubeMap_invOpenTube C y.1)

/-! ## The transfer identity on chain complexes -/

/-- **The inverse tubular map followed by the tubular map is the excision inclusion.** -/
theorem invChainMap_comp_tubeChainMap {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (C : TubeChart E ε) (K : Set (NormalDiscSub E ε)) :
    invChainMap C K ≫ tubeChainMap C K = excisionMap (E := E) K := by
  calc invChainMap C K ≫ tubeChainMap C K
      = Work.Cohomology.relChainsMapOf (TopCat.of ↥(openTubeSet E ε))
          (TopCat.of (NormalDiscSub E ε)) (tubeRelSub (E := E) K) (discRelSub (E := E) K)
          (invOpenTubeTop C) (invSubTop C K) (by ext y <;> rfl)
        ≫ Work.Cohomology.relChainsMapOf (TopCat.of (NormalDiscSub E ε))
          (TopCat.of (Euc (8 + k))) (discRelSub (E := E) K) (tubeImage (E := E) K)ᶜ
          (tubeMapTop (E := E)) (tubeSubTop C K) (by ext y; rfl) := rfl
    _ = Work.Cohomology.relChainsMapOf (TopCat.of ↥(openTubeSet E ε))
          (TopCat.of (Euc (8 + k))) (tubeRelSub (E := E) K) (tubeImage (E := E) K)ᶜ
          (invOpenTubeTop C ≫ tubeMapTop (E := E)) (invSubTop C K ≫ tubeSubTop C K)
          (by ext y; rfl) := by
        exact Work.Cohomology.relChainsMapOf_comp _ _ _ _ _ _ _ _ _ _
    _ = Work.Cohomology.relChainsMapOf (TopCat.of ↥(openTubeSet E ε))
          (TopCat.of (Euc (8 + k))) (tubeRelSub (E := E) K) (tubeImage (E := E) K)ᶜ
          (Work.Cohomology.subtypeIncl (TopCat.of (Euc (8 + k))) (openTubeSet E ε))
          (Work.Cohomology.inclInterA (TopCat.of (Euc (8 + k))) (openTubeSet E ε)
            (tubeImage (E := E) K)ᶜ)
          (by ext y; rfl) :=
        relChainsMapOf_congr_tub _ _ (invOpenTubeTop_comp_tubeMapTop C)
          (invSubTop_comp_tubeSubTop C K) (by ext y; rfl) (by ext y; rfl)
    _ = excisionMap (E := E) K := by
        rw [excisionMap, Work.Cohomology.relChainsMap]
        rfl

/-- Naturality of the inverse chain map with respect to enlarging the relative subsets. -/
theorem invChainMap_relCokerMap {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (C : TubeChart E ε) {K K' : Set (NormalDiscSub E ε)} (h : K ⊆ K') :
    invChainMap C K' ≫ Work.Cohomology.relCokerMap (TopCat.of (NormalDiscSub E ε))
        (discRelSub (E := E) K') (discRelSub (E := E) K) (fun y hy hc => hy (h hc))
      = Work.Cohomology.relCokerMap (TopCat.of ↥(openTubeSet E ε))
          (tubeRelSub (E := E) K') (tubeRelSub (E := E) K)
          (fun y hy hyy => hy (by
            rcases hyy with ⟨q, hq, hqe⟩
            exact ⟨q, h hq, hqe⟩))
        ≫ invChainMap C K := by
  exact relChainsMapOf_relCokerMap_tub (X := TopCat.of ↥(openTubeSet E ε))
    (Y := TopCat.of (NormalDiscSub E ε))
    (A := tubeRelSub (E := E) K) (A' := tubeRelSub (E := E) K')
    (B := discRelSub (E := E) K) (B' := discRelSub (E := E) K')
    (hA := fun y hy hyy => hy (by
      rcases hyy with ⟨q, hq, hqe⟩
      exact ⟨q, h hq, hqe⟩))
    (hB := fun y hy hc => hy (h hc)) (f := invOpenTubeTop C)
    (g := invSubTop C K) (w := by ext y <;> rfl)
    (g' := invSubTop C K') (w' := by ext y <;> rfl)

/-! ## The homeomorphism of the open tube with the open disc bundle -/

/-- **The inverse of the tubular map is a homeomorphism from the open tube onto the open disc
bundle.** -/
noncomputable def tubeOpenHomeo {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (C : TubeChart E ε) :
    ↥(openTubeSet E ε) ≃ₜ ↥(openDiscSub (E := E) ε) where
  toFun y := ⟨(invOpenTube C y : NormalDiscSub E ε), normalNorm_inv_lt C y.2⟩
  invFun q := ⟨tubeMap E (q.1 : NormalTotal E), mem_openTubeSet_iff.mpr ⟨q.1, q.2, rfl⟩⟩
  left_inv y := Subtype.ext (tubeMap_invOpenTube C y)
  right_inv q := Subtype.ext (Subtype.ext (C.inv_tubeMap q.1 (le_of_lt q.2)))
  continuous_toFun := Continuous.subtype_mk ((invOpenTube C).continuous)
    (fun y => normalNorm_inv_lt C y.2)
  continuous_invFun := Continuous.subtype_mk
    ((continuous_tubeMap E).comp (continuous_subtype_val.comp continuous_subtype_val))
    (fun q => mem_openTubeSet_iff.mpr ⟨q.1, q.2, rfl⟩)

/-- A homeomorphism of pairs induces a quasi-isomorphism of the relative chain complexes. -/
theorem isIso_relChainsMapOf_homeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : X ≃ₜ Y) (A : Set X) (B : Set Y) (hA : ∀ x, x ∈ A ↔ φ x ∈ B) (n : ℕ)
    (w : Work.Cohomology.subtypeIncl (TopCat.of X) A ≫ (TopCat.ofHom φ.toHomotopyEquiv.toFun)
      = (TopCat.ofHom (Work.Orient.Boundary.homeomorphRestrict φ A B hA).toHomotopyEquiv.toFun)
        ≫ Work.Cohomology.subtypeIncl (TopCat.of Y) B) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf (TopCat.of X)
      (TopCat.of Y) A B (TopCat.ofHom φ.toHomotopyEquiv.toFun)
      (TopCat.ofHom (Work.Orient.Boundary.homeomorphRestrict φ A B hA).toHomotopyEquiv.toFun)
      w) n) := by
  let ψ := Work.Orient.Boundary.homeomorphRestrict φ A B hA
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom φ.toHomotopyEquiv.toFun
  let g : TopCat.of A ⟶ TopCat.of B := TopCat.ofHom ψ.toHomotopyEquiv.toFun
  have hw : Work.Cohomology.subtypeIncl (TopCat.of X) A ≫ f
      = g ≫ Work.Cohomology.subtypeIncl (TopCat.of Y) B := by ext z; rfl
  have hfq : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) f) k) :=
    fun k => Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv
      (X := TopCat.of X) (Y := TopCat.of Y) φ.toHomotopyEquiv k
  have hgq : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) g) k) :=
    fun k => Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv
      (X := TopCat.of A) (Y := TopCat.of B) ψ.toHomotopyEquiv k
  have := Work.Cohomology.relChainsMapOf_homologyMap_isIso (X := TopCat.of X)
    (Y := TopCat.of Y) A B f g hw n hfq hgq
  infer_instance

/-! ## The excision map is a homology isomorphism -/

/-- **Excision**: the inclusion of pairs `(U_ε, U_ε∖K') ↪ (ℝ^N, ℝ^N∖K')` is an isomorphism on
relative homology, for `K` compact with all norms `< ε`. -/
theorem isIso_homologyMap_excisionMap {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (C : TubeChart E ε) (K : Set (NormalDiscSub E ε))
    (hK : ∀ q ∈ K, normalNorm E (q : NormalTotal E) < ε) (hKc : IsCompact K) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (excisionMap (E := E) K) n) := by
  have hsub : tubeImage (E := E) K ⊆ openTubeSet E ε := tubeImage_subset_openTube C hK
  have hA : IsOpen ((tubeImage (E := E) K)ᶜ) := by
    have hc : IsCompact (tubeImage (E := E) K) :=
      hKc.image ((continuous_tubeMap E).comp continuous_subtype_val)
    exact hc.isClosed.isOpen_compl
  have hcov : openTubeSet E ε ∪ (tubeImage (E := E) K)ᶜ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    by_cases hy : y ∈ tubeImage (E := E) K
    · exact Or.inl (hsub hy)
    · exact Or.inr hy
  exact Work.Cohomology.excision_relChainsMap_isIso (TopCat.of (Euc (8 + k)))
    (openTubeSet E ε) ((tubeImage (E := E) K)ᶜ) C.isOpen_openTube hA hcov n

/-! ## The inverse chain map is a homology isomorphism -/

/-- **The inverse tubular chain map is an isomorphism on homology.** -/
theorem invChainMap_homologyMap_isIso
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (C : TubeChart E ε) (K : Set (NormalDiscSub E ε))
    (hK : ∀ q ∈ K, normalNorm E (q : NormalTotal E) < ε) (hKc : IsCompact K) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (invChainMap C K) n) := by
  let φ : ↥(openTubeSet E ε) ≃ₜ ↥(openDiscSub (E := E) ε) := tubeOpenHomeo C
  let OdiscRel : Set ↥(openDiscSub (E := E) ε) :=
    {y | (y : NormalDiscSub E ε) ∈ discRelSub (E := E) K}
  have hA : ∀ y : ↥(openTubeSet E ε), y ∈ tubeRelSub (E := E) K ↔ φ y ∈ OdiscRel := by
    intro y
    change (y : Euc (8 + k)) ∉ tubeImage (E := E) K ↔
      (invOpenTube C y : NormalDiscSub E ε) ∉ K
    constructor
    · intro hy hyK
      exact hy ⟨(invOpenTube C y : NormalDiscSub E ε), hyK, tubeMap_invOpenTube C y⟩
    · intro hy hyK
      obtain ⟨q, hq, hqe⟩ := mem_tubeImage.mp hyK
      have hqi : q = (invOpenTube C y : NormalDiscSub E ε) :=
        tubeMap_injective C (by
          show tubeMap E (q : NormalTotal E) =
            tubeMap E ((invOpenTube C y : NormalDiscSub E ε) : NormalTotal E)
          rw [hqe, tubeMap_invOpenTube C y])
      exact hy (hqi ▸ hq)
  let ψ := Work.Orient.Boundary.homeomorphRestrict φ (tubeRelSub (E := E) K) OdiscRel hA
  have w1 : Work.Cohomology.subtypeIncl (TopCat.of ↥(openTubeSet E ε)) (tubeRelSub (E := E) K)
        ≫ (TopCat.ofHom φ.toHomotopyEquiv.toFun)
      = (TopCat.ofHom ψ.toHomotopyEquiv.toFun)
        ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥(openDiscSub (E := E) ε)) OdiscRel := by
    apply TopCat.hom_ext; apply ContinuousMap.ext; intro z; rfl
  have htop : (TopCat.ofHom φ.toHomotopyEquiv.toFun
      ≫ Work.Cohomology.subtypeIncl (TopCat.of (NormalDiscSub E ε)) (openDiscSub (E := E) ε))
      = invOpenTubeTop C := by
    apply TopCat.hom_ext; apply ContinuousMap.ext; intro z; rfl
  have hsub : (TopCat.ofHom ψ.toHomotopyEquiv.toFun
      ≫ Work.Cohomology.inclInterA (TopCat.of (NormalDiscSub E ε)) (openDiscSub (E := E) ε)
          (discRelSub (E := E) K))
      = invSubTop C K := by
    apply TopCat.hom_ext; apply ContinuousMap.ext; intro z; rfl
  let map1 := Work.Cohomology.relChainsMapOf (TopCat.of ↥(openTubeSet E ε))
    (TopCat.of ↥(openDiscSub (E := E) ε)) (tubeRelSub (E := E) K) OdiscRel
    (TopCat.ofHom φ.toHomotopyEquiv.toFun) (TopCat.ofHom ψ.toHomotopyEquiv.toFun) w1
  have h1 : IsIso (HomologicalComplex.homologyMap map1 n) :=
    isIso_relChainsMapOf_homeo φ (tubeRelSub (E := E) K) OdiscRel hA n w1
  haveI h2 : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap
      (TopCat.of (NormalDiscSub E ε)) (openDiscSub (E := E) ε) (discRelSub (E := E) K)) n) := by
    refine Work.Cohomology.excision_relChainsMap_isIso (TopCat.of (NormalDiscSub E ε))
      (openDiscSub (E := E) ε) (discRelSub (E := E) K) (isOpen_openDiscSub ε) ?_ ?_ n
    · rw [discRelSub]; exact hKc.isClosed.isOpen_compl
    · apply Set.eq_univ_of_forall
      intro y
      by_cases hy : y ∈ K
      · exact Or.inl (hK y hy)
      · exact Or.inr hy
  have hfac : invChainMap C K
      = map1 ≫ Work.Cohomology.relChainsMap (TopCat.of (NormalDiscSub E ε))
          (openDiscSub (E := E) ε) (discRelSub (E := E) K) := by
    have wB : Work.Cohomology.subtypeIncl (TopCat.of ↥(openDiscSub (E := E) ε)) OdiscRel
          ≫ (Work.Cohomology.subtypeIncl (TopCat.of (NormalDiscSub E ε))
              (openDiscSub (E := E) ε))
        = (Work.Cohomology.inclInterA (TopCat.of (NormalDiscSub E ε)) (openDiscSub (E := E) ε)
              (discRelSub (E := E) K))
          ≫ Work.Cohomology.subtypeIncl (TopCat.of (NormalDiscSub E ε))
              (discRelSub (E := E) K) := by
      apply TopCat.hom_ext; apply ContinuousMap.ext; intro z; rfl
    have w2 : Work.Cohomology.subtypeIncl (TopCat.of ↥(openTubeSet E ε)) (tubeRelSub (E := E) K)
          ≫ ((TopCat.ofHom φ.toHomotopyEquiv.toFun)
              ≫ Work.Cohomology.subtypeIncl (TopCat.of (NormalDiscSub E ε))
                  (openDiscSub (E := E) ε))
        = ((TopCat.ofHom ψ.toHomotopyEquiv.toFun)
              ≫ Work.Cohomology.inclInterA (TopCat.of (NormalDiscSub E ε))
                  (openDiscSub (E := E) ε) (discRelSub (E := E) K))
          ≫ Work.Cohomology.subtypeIncl (TopCat.of (NormalDiscSub E ε))
              (discRelSub (E := E) K) := by
      apply TopCat.hom_ext; apply ContinuousMap.ext; intro z; rfl
    have h2 := Work.Cohomology.relChainsMapOf_comp
      (X := TopCat.of ↥(openTubeSet E ε)) (Y := TopCat.of ↥(openDiscSub (E := E) ε))
      (Z := TopCat.of (NormalDiscSub E ε))
      (A := tubeRelSub (E := E) K) (B := OdiscRel) (C := discRelSub (E := E) K)
      (f := TopCat.ofHom φ.toHomotopyEquiv.toFun)
      (g := TopCat.ofHom ψ.toHomotopyEquiv.toFun) (w := w1)
      (f' := Work.Cohomology.subtypeIncl (TopCat.of (NormalDiscSub E ε))
        (openDiscSub (E := E) ε))
      (g' := Work.Cohomology.inclInterA (TopCat.of (NormalDiscSub E ε))
        (openDiscSub (E := E) ε) (discRelSub (E := E) K))
      (w' := wB) (w'' := w2)
    calc invChainMap C K
        = Work.Cohomology.relChainsMapOf (TopCat.of ↥(openTubeSet E ε))
            (TopCat.of (NormalDiscSub E ε)) (tubeRelSub (E := E) K) (discRelSub (E := E) K)
            (invOpenTubeTop C) (invSubTop C K) (by ext y <;> rfl) := rfl
      _ = Work.Cohomology.relChainsMapOf (TopCat.of ↥(openTubeSet E ε))
            (TopCat.of (NormalDiscSub E ε)) (tubeRelSub (E := E) K) (discRelSub (E := E) K)
            (TopCat.ofHom φ.toHomotopyEquiv.toFun
              ≫ Work.Cohomology.subtypeIncl (TopCat.of (NormalDiscSub E ε))
                  (openDiscSub (E := E) ε))
            (TopCat.ofHom ψ.toHomotopyEquiv.toFun
              ≫ Work.Cohomology.inclInterA (TopCat.of (NormalDiscSub E ε))
                  (openDiscSub (E := E) ε) (discRelSub (E := E) K))
            w2 := (relChainsMapOf_congr_tub _ _ htop hsub w2 (by ext y <;> rfl)).symm
      _ = map1 ≫ Work.Cohomology.relChainsMap (TopCat.of (NormalDiscSub E ε))
            (openDiscSub (E := E) ε) (discRelSub (E := E) K) := h2.symm
  rw [hfac, HomologicalComplex.homologyMap_comp]
  infer_instance

/-- A generator of the relative homology of the open tube pair maps to a generator of the relative
homology of the disc bundle pair, for `K` compact with all norms `< ε`. -/
theorem span_top_homologyMap_invChainMap
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (C : TubeChart E ε) (K : Set (NormalDiscSub E ε))
    (hK : ∀ q ∈ K, normalNorm E (q : NormalTotal E) < ε) (hKc : IsCompact K)
    (u : (Work.Cohomology.relChains (TopCat.of ↥(openTubeSet E ε))
      (tubeRelSub (E := E) K)).homology (8 + k))
    (hu : Submodule.span ℤ ({u} : Set _) = ⊤) :
    Submodule.span ℤ
      ({(HomologicalComplex.homologyMap (invChainMap C K) (8 + k)).hom u} : Set _) = ⊤ := by
  haveI := invChainMap_homologyMap_isIso C K hK hKc (8 + k)
  have hsurj := (ConcreteCategory.bijective_of_isIso
    (HomologicalComplex.homologyMap (invChainMap C K) (8 + k))).2
  have hspan : Submodule.span ℤ
      ({(HomologicalComplex.homologyMap (invChainMap C K) (8 + k)).hom u} : Set _)
      = Submodule.map (HomologicalComplex.homologyMap (invChainMap C K) (8 + k)).hom
          (Submodule.span ℤ ({u} : Set _)) := by
    rw [Submodule.map_span, Set.image_singleton]
  rw [hspan, hu, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr hsurj

theorem tubeTransferChain {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k] {ε : ℝ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (C : Work.Tubular.TubeChart E ε) :
    (∀ K : Set (Work.Tubular.NormalDiscSub E ε),
        CategoryTheory.CategoryStruct.comp (Work.Tubular.invChainMap C K) (Work.Tubular.tubeChainMap C K)
          = Work.Tubular.excisionMap (E := E) K) ∧
    (∀ (K K' : Set (Work.Tubular.NormalDiscSub E ε)) (h : K ⊆ K'),
        CategoryTheory.CategoryStruct.comp (Work.Tubular.invChainMap C K') (Work.Cohomology.relCokerMap
            (TopCat.of (Work.Tubular.NormalDiscSub E ε))
            (Work.Tubular.discRelSub (E := E) K') (Work.Tubular.discRelSub (E := E) K)
            (fun y hy hc => hy (h hc)))
          = CategoryTheory.CategoryStruct.comp (Work.Cohomology.relCokerMap
              (TopCat.of ↥(Work.Tubular.openTubeSet E ε))
              (Work.Tubular.tubeRelSub (E := E) K') (Work.Tubular.tubeRelSub (E := E) K)
              (fun y hy hyy => hy (by
                rcases hyy with ⟨q, hq, hqe⟩
                exact ⟨q, h hq, hqe⟩))
            ) (Work.Tubular.invChainMap C K)) ∧
    (∀ (K : Set (Work.Tubular.NormalDiscSub E ε)),
        (∀ q ∈ K, Work.Tubular.normalNorm E (q : Work.Tubular.NormalTotal E) < ε) →
        IsCompact K →
        ∀ u : (Work.Cohomology.relChains (TopCat.of ↥(Work.Tubular.openTubeSet E ε))
          (Work.Tubular.tubeRelSub (E := E) K)).homology (8 + k),
        Submodule.span ℤ ({u} : Set _) = ⊤ →
        Submodule.span ℤ ({((HomologicalComplex.homologyMap (Work.Tubular.invChainMap C K)
          (8 + k)).hom u)} : Set _) = ⊤) := by
  refine ⟨fun K => invChainMap_comp_tubeChainMap C K, fun K K' h => invChainMap_relCokerMap C h,
    fun K hK hKc u hu => span_top_homologyMap_invChainMap C K hK hKc u hu⟩

end

end Work.Tubular

import Submission.Work.Tubular.relKronH_natural
import Submission.Work.Tubular.Assembly
import Submission.Work.Tubular.tubeCollapseClass_span_top
import Submission.Work.Tubular.hurewiczClassOf_add_comm

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Limits
open scoped Topology

open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.Tubular

noncomputable section

open Work.Cohomology

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-! ## The comparison of the relative pairing with the world of `(ν, ν∖0)` -/

/-- The complement of `∞` in `ν⁺`. -/
abbrev infCompl (E : EmbeddingData V (8 + k)) : Set (OnePoint (NormalTotal E)) :=
  {OnePoint.infty}ᶜ

/-- The intersection of `A = (ν∖0) ∪ {∞}` with the complement of `∞`. -/
abbrev excSub (E : EmbeddingData V (8 + k)) : Set ↥(infCompl E) :=
  {y : ↥(infCompl E) | y.1 ∈ onePointNonzero E}

/-- The inclusion `{∞}ᶜ ⊆ ν⁺`, as a continuous map. -/
def infComplIncl (E : EmbeddingData V (8 + k)) :
    C(↥(infCompl E), OnePoint (NormalTotal E)) :=
  ⟨fun y => y.1, continuous_subtype_val⟩


/-- **A homeomorphism of pairs induces an isomorphism on relative homology**, in the spelling of
`Work.Cohomology.relChainsMapOf` (the general form of one half of
`Work.Tubular.nonempty_relChains_homology_homeo`). -/
theorem isIso_relChainsMapOf_homeoSub {X Y : TopCat} (e : X ≃ₜ Y) {A : Set X} {B : Set Y}
    (hAB : ∀ x : X, x ∈ A ↔ e x ∈ B)
    (hw : CategoryTheory.CategoryStruct.comp (subtypeIncl X A) (TopCat.ofHom e)
      = CategoryTheory.CategoryStruct.comp (TopCat.ofHom (e.subtype hAB)) (subtypeIncl Y B))
    (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (relChainsMapOf X Y A B (TopCat.ofHom e) (TopCat.ofHom (e.subtype hAB)) hw) n) := by
  have h1 : TopCat.Homotopy (CategoryTheory.CategoryStruct.comp (TopCat.ofHom e)
      (TopCat.ofHom (e.symm : C(↑Y, ↑X)))) (𝟙 X) := by
    have heq : (CategoryTheory.CategoryStruct.comp (TopCat.ofHom e)
        (TopCat.ofHom (e.symm : C(↑Y, ↑X))) : X ⟶ X) = 𝟙 X := by
      ext x
      exact e.symm_apply_apply x
    rw [heq]
    exact ContinuousMap.Homotopy.refl _
  have h2 : TopCat.Homotopy (CategoryTheory.CategoryStruct.comp
      (TopCat.ofHom (e.symm : C(↑Y, ↑X))) (TopCat.ofHom e)) (𝟙 Y) := by
    have heq : (CategoryTheory.CategoryStruct.comp (TopCat.ofHom (e.symm : C(↑Y, ↑X)))
        (TopCat.ofHom e) : Y ⟶ Y) = 𝟙 Y := by
      ext x
      exact e.apply_symm_apply x
    rw [heq]
    exact ContinuousMap.Homotopy.refl _
  have hf : ∀ j, IsIso (HomologicalComplex.homologyMap (chainMap ℤ X Y (TopCat.ofHom e)) j) :=
    fun j => homologyEquiv ℤ X Y (TopCat.ofHom e) (TopCat.ofHom (e.symm : C(↑Y, ↑X))) h1 h2 j
  have h1' : TopCat.Homotopy (CategoryTheory.CategoryStruct.comp (TopCat.ofHom (e.subtype hAB))
      (TopCat.ofHom ((e.subtype hAB).symm : C(↥B, ↥A)))) (𝟙 (TopCat.of A)) := by
    have heq : (CategoryTheory.CategoryStruct.comp (TopCat.ofHom (e.subtype hAB))
        (TopCat.ofHom ((e.subtype hAB).symm : C(↥B, ↥A))) : TopCat.of A ⟶ TopCat.of A)
        = 𝟙 (TopCat.of A) := by
      ext x
      simpa using (e.subtype hAB).symm_apply_apply x
    rw [heq]
    exact ContinuousMap.Homotopy.refl _
  have h2' : TopCat.Homotopy (CategoryTheory.CategoryStruct.comp
      (TopCat.ofHom ((e.subtype hAB).symm : C(↥B, ↥A)))
      (TopCat.ofHom (e.subtype hAB))) (𝟙 (TopCat.of B)) := by
    have heq : (CategoryTheory.CategoryStruct.comp (TopCat.ofHom ((e.subtype hAB).symm : C(↥B, ↥A)))
        (TopCat.ofHom (e.subtype hAB)) : TopCat.of B ⟶ TopCat.of B) = 𝟙 (TopCat.of B) := by
      ext x
      simpa using (e.subtype hAB).apply_symm_apply x
    rw [heq]
    exact ContinuousMap.Homotopy.refl _
  have hg : ∀ j, IsIso (HomologicalComplex.homologyMap
      (chainMap ℤ (TopCat.of A) (TopCat.of B) (TopCat.ofHom (e.subtype hAB))) j) :=
    fun j => homologyEquiv ℤ (TopCat.of A) (TopCat.of B) (TopCat.ofHom (e.subtype hAB))
      (TopCat.ofHom ((e.subtype hAB).symm : C(↥B, ↥A))) h1' h2' j
  exact relChainsMapOf_homologyMap_isIso A B (TopCat.ofHom e) (TopCat.ofHom (e.subtype hAB))
    hw n hf hg

@[simp] theorem infComplIncl_apply (E : EmbeddingData V (8 + k)) (y : ↥(infCompl E)) :
    infComplIncl E y = y.1 := rfl

/-- The union `{∞}ᶜ ∪ A` is everything. -/
theorem infCompl_union_onePointNonzero (E : EmbeddingData V (8 + k)) :
    infCompl E ∪ onePointNonzero E = Set.univ := by
  rw [infCompl, onePointNonzero,
    Set.union_comm (OnePoint.some '' normalNonzero E) {OnePoint.infty},
    ← Set.union_assoc, Set.compl_union_self]
  exact Set.univ_union _

/-- The compatibility of `{∞}ᶜ ↪ ν⁺` with the inclusions of the punctured parts. -/
theorem excSpec (E : EmbeddingData V (8 + k)) :
    CategoryTheory.CategoryStruct.comp
        (subtypeIncl (TopCat.of ↥(infCompl E)) (excSub E))
        (TopCat.ofHom (infComplIncl E))
      = CategoryTheory.CategoryStruct.comp
        (inclInterA (TopCat.of (OnePoint (NormalTotal E))) (infCompl E) (onePointNonzero E))
        (subtypeIncl (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E)) := by
  apply TopCat.ext
  intro y
  rfl

/-- **The chain map of the excision of `{∞}`**, i.e. the inclusion of pairs
`({∞}ᶜ, {∞}ᶜ ∩ A) → (ν⁺, A)`. -/
def excChain (E : EmbeddingData V (8 + k)) :
    relChains (TopCat.of ↥(infCompl E)) (excSub E) ⟶
      relChains (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E) :=
  relChainsMapOf (TopCat.of ↥(infCompl E)) (TopCat.of (OnePoint (NormalTotal E)))
    (excSub E) (onePointNonzero E)
    (TopCat.ofHom (infComplIncl E))
    (inclInterA (TopCat.of (OnePoint (NormalTotal E))) (infCompl E) (onePointNonzero E))
    (excSpec E)

/-- **The excision of `{∞}` is an isomorphism on relative homology.** -/
theorem isIso_excChain (E : EmbeddingData V (8 + k)) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (excChain E) n) := by
  rw [excChain]
  exact excision_relChainsMap_isIso (TopCat.of (OnePoint (NormalTotal E))) (infCompl E)
    (onePointNonzero E) OnePoint.isClosed_infty.isOpen_compl (isOpen_onePointNonzero E)
    (infCompl_union_onePointNonzero E) n

/-- **The excision transfer of the relative Kronecker pairing.** -/
theorem relKronH_excision (E : EmbeddingData V (8 + k)) (n : ℕ)
    (β : Work.Thom.RelCoh ℤ n (OnePoint (NormalTotal E)) (onePointNonzero E))
    (c : (relChains (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E)).homology n)
    (cU : (relChains (TopCat.of ↥(infCompl E)) (excSub E)).homology n)
    (hcU : (HomologicalComplex.homologyMap (excChain E) n).hom cU = c) :
    relKronH (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E) n β c
      = relKronH (TopCat.of ↥(infCompl E)) (excSub E) n
          ((Work.Thom.relCohMap (infComplIncl E)
            (excSub E) (onePointNonzero E) (fun y hy => hy) ℤ n).hom β) cU := by
  have h := relKronH_natural
    (X := TopCat.of ↥(infCompl E)) (Y := TopCat.of (OnePoint (NormalTotal E)))
    (A := excSub E) (B := onePointNonzero E)
    (TopCat.ofHom (infComplIncl E))
    (inclInterA (TopCat.of (OnePoint (NormalTotal E))) (infCompl E) (onePointNonzero E))
    (fun y hy => hy) (excSpec E) n β cU
  rw [excChain] at hcU
  rw [h, hcU]

/-! ## The homeomorphism `ν ≅ {∞}ᶜ` -/

/-- The canonical homeomorphism from the normal bundle onto the complement of `∞`. -/
noncomputable def homeoV (E : EmbeddingData V (8 + k)) :
    NormalTotal E ≃ₜ ↥(infCompl E) :=
  onePointRangeHomeo (NormalTotal E)

@[simp] theorem homeoV_apply (E : EmbeddingData V (8 + k)) (x : NormalTotal E) :
    ((homeoV E x : ↥(infCompl E)) : OnePoint (NormalTotal E)) = OnePoint.some x :=
  onePointRangeHomeo_apply x

/-- **`homeoV` carries `ν∖0` onto `{∞}ᶜ ∩ A`.** -/
theorem homeoV_mem (E : EmbeddingData V (8 + k)) (x : NormalTotal E) :
    x ∈ normalNonzero E ↔ homeoV E x ∈ excSub E := by
  have hco : ((homeoV E x : ↥(infCompl E)) : OnePoint (NormalTotal E)) = OnePoint.some x :=
    homeoV_apply E x
  have hmem : (homeoV E x ∈ excSub E) ↔ (OnePoint.some x ∈ onePointNonzero E) := by
    show (homeoV E x).1 ∈ onePointNonzero E ↔ OnePoint.some x ∈ onePointNonzero E
    rw [hco]
  rw [hmem]
  constructor
  · intro hx
    exact mem_onePointNonzero.mpr (Or.inr ⟨x, hx, rfl⟩)
  · intro hx
    rcases mem_onePointNonzero.mp hx with hh | ⟨w, hw, hwy⟩
    · exact absurd hh (OnePoint.coe_ne_infty x)
    · have hwx : w = x := OnePoint.coe_injective hwy
      rw [← hwx]
      exact hw

/-- The map of pairs induced by `homeoV` on the punctured parts. -/
def homeoSubMap (E : EmbeddingData V (8 + k)) :
    TopCat.of ↥(normalNonzero E) ⟶ TopCat.of ↥(excSub E) :=
  TopCat.ofHom ((homeoV E).subtype (homeoV_mem E))

/-- The compatibility of `homeoV` with the inclusions of the punctured parts. -/
theorem homeoSubMap_spec (E : EmbeddingData V (8 + k)) :
    CategoryTheory.CategoryStruct.comp
        (subtypeIncl (TopCat.of (NormalTotal E)) (normalNonzero E)) (TopCat.ofHom (homeoV E))
      = CategoryTheory.CategoryStruct.comp (homeoSubMap E)
        (subtypeIncl (TopCat.of ↥(infCompl E)) (excSub E)) := by
  apply TopCat.ext
  intro a
  rfl

/-- **The chain map of the homeomorphism of pairs `(ν, ν∖0) ≅ ({∞}ᶜ, {∞}ᶜ ∩ A)`.** -/
def homeoChain (E : EmbeddingData V (8 + k)) :
    relChains (TopCat.of (NormalTotal E)) (normalNonzero E) ⟶
      relChains (TopCat.of ↥(infCompl E)) (excSub E) :=
  relChainsMapOf (TopCat.of (NormalTotal E)) (TopCat.of ↥(infCompl E)) (normalNonzero E)
    (excSub E) (TopCat.ofHom (homeoV E))
    (TopCat.ofHom ((homeoV E).subtype (homeoV_mem E))) (homeoSubMap_spec E)

/-- **The homeomorphism of pairs is an isomorphism on relative homology.** -/
theorem isIso_homeoChain (E : EmbeddingData V (8 + k)) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (homeoChain E) n) :=
  isIso_relChainsMapOf_homeoSub (X := TopCat.of (NormalTotal E)) (Y := TopCat.of ↥(infCompl E))
    (A := normalNonzero E) (B := excSub E) (homeoV E) (homeoV_mem E) (homeoSubMap_spec E) n

/-- **The homeomorphism transfer of the relative Kronecker pairing.** -/
theorem relKronH_homeo (E : EmbeddingData V (8 + k)) (n : ℕ)
    (b : Work.Thom.RelCoh ℤ n ↥(infCompl E) (excSub E))
    (cν : (relChains (TopCat.of (NormalTotal E)) (normalNonzero E)).homology n)
    (cU : (relChains (TopCat.of ↥(infCompl E)) (excSub E)).homology n)
    (hcU : (HomologicalComplex.homologyMap (homeoChain E) n).hom cν = cU) :
    relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) n
        ((HomologicalComplex.homologyMap (relComplexMap ℤ (normalNonzero E) (excSub E)
          (TopCat.ofHom (homeoV E)) (fun x hx => (homeoV_mem E x).mp hx)) n).hom b) cν
      = relKronH (TopCat.of ↥(infCompl E)) (excSub E) n b cU := by
  have h := relKronH_natural
    (X := TopCat.of (NormalTotal E)) (Y := TopCat.of ↥(infCompl E))
    (A := normalNonzero E) (B := excSub E)
    (TopCat.ofHom (homeoV E)) (TopCat.ofHom ((homeoV E).subtype (homeoV_mem E)))
    (fun x hx => (homeoV_mem E x).mp hx) (homeoSubMap_spec E) n b cν
  rw [homeoChain] at hcU
  rw [hcU] at h
  exact h

/-! ## The comparison isomorphism -/

/-- **The comparison `H_n(ν, ν∖0) ≅ H_n(ν⁺, A)`** of the chapter, assembled from the excision of
`{∞}` and the homeomorphism of pairs. -/
noncomputable def compIso (E : EmbeddingData V (8 + k)) (n : ℕ) :
    (relChains (TopCat.of (NormalTotal E)) (normalNonzero E)).homology n ≅
      (relChains (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E)).homology n := by
  haveI h1 := isIso_homeoChain E n
  haveI h2 := isIso_excChain E n
  exact Iso.trans (asIso (HomologicalComplex.homologyMap (homeoChain E) n))
    (asIso (HomologicalComplex.homologyMap (excChain E) n))

/-- The composite pullback of relative cohomology along the comparison. -/
noncomputable def compPull (E : EmbeddingData V (8 + k)) (n : ℕ) :
    Work.Thom.RelCoh ℤ n (OnePoint (NormalTotal E)) (onePointNonzero E) →ₗ[ℤ]
      Work.Thom.RelCoh ℤ n (NormalTotal E) (normalNonzero E) :=
  { toFun := fun β =>
      (HomologicalComplex.homologyMap (relComplexMap ℤ (normalNonzero E) (excSub E)
        (TopCat.ofHom (homeoV E)) (fun x hx => (homeoV_mem E x).mp hx)) n).hom
        ((Work.Thom.relCohMap (infComplIncl E) (excSub E) (onePointNonzero E)
          (fun y hy => hy) ℤ n).hom β)
    map_add' := fun β γ => by simp
    map_smul' := fun c β => by simp }

/-- **The comparison transfer of the relative Kronecker pairing.** -/
theorem relKronH_comparison (E : EmbeddingData V (8 + k)) (n : ℕ)
    (β : Work.Thom.RelCoh ℤ n (OnePoint (NormalTotal E)) (onePointNonzero E))
    (cν : (relChains (TopCat.of (NormalTotal E)) (normalNonzero E)).homology n) :
    relKronH (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E) n β
        ((compIso E n).hom cν)
      = relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) n (compPull E n β) cν := by
  haveI h1 := isIso_homeoChain E n
  haveI h2 := isIso_excChain E n
  set cU := (asIso (HomologicalComplex.homologyMap (homeoChain E) n)).hom cν with hcUdef
  have hhom : ((compIso E n).hom) cν = (HomologicalComplex.homologyMap (excChain E) n).hom cU :=
    rfl
  have hE := relKronH_excision E n β ((HomologicalComplex.homologyMap (excChain E) n).hom cU) cU rfl
  have hH := relKronH_homeo E n
    ((Work.Thom.relCohMap (infComplIncl E) (excSub E) (onePointNonzero E)
      (fun y hy => hy) ℤ n).hom β) cν cU (by rw [hcUdef]; rfl)
  rw [hhom]
  exact hE.trans (hH.symm.trans (by rfl))

/-! ## The class of the collapse in `H_{8+k}(ν, ν∖0)` -/

/-- **The class of the Pontryagin–Thom collapse in `H_{8+k}(ν, ν∖0)`**, i.e. the image of the
Hurewicz class of the metric-free collapse `Work.Tubular.tubeGenLoopOnePoint` (of degree `8+k`, the
degree in which `Work.Tubular.alphaV` produces it) under the comparison `compIso`.  This is the
class `c` of the local degree
(`Work.Tubular.TubeLocalDegree`, `Work.ThomBordism.tubeLocalDegreeGlobalSign`). -/
noncomputable def collapseClassRel {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : EmbeddingData V (8 + k)} {ε : ℝ} (C : TubeChart E ε)
    (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R) :
    (relChains (TopCat.of (NormalTotal E)) (normalNonzero E)).homology (8 + k) :=
  (compIso E (8 + k)).inv
    ((HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
      (inclChains (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E))) (8 + k)).hom
      (Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty
        (tubeGenLoopOnePoint C g hg hR hbox)))

/-- **The transfer for the collapse class.** -/
theorem relKronH_collapseClassRel {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : EmbeddingData V (8 + k)} {ε : ℝ} (C : TubeChart E ε)
    (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    (β : Work.Thom.RelCoh ℤ (8 + k) (OnePoint (NormalTotal E)) (onePointNonzero E)) :
    relKronH (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E) (8 + k) β
        ((HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
          (inclChains (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E))) (8 + k)).hom
          (Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty
            (tubeGenLoopOnePoint C g hg hR hbox)))
      = relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (8 + k)
          (compPull E (8 + k) β) (collapseClassRel C g hg hR hbox) := by
  haveI h1 := isIso_homeoChain E (8 + k)
  haveI h2 := isIso_excChain E (8 + k)
  have hc : (compIso E (8 + k)).hom (collapseClassRel C g hg hR hbox)
      = (HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
          (inclChains (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E))) (8 + k)).hom
          (Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty
            (tubeGenLoopOnePoint C g hg hR hbox)) := by
    rw [collapseClassRel]
    exact Iso.inv_hom_id_apply (compIso E (8 + k)) _
  rw [← hc]
  exact relKronH_comparison E (8 + k) β (collapseClassRel C g hg hR hbox)

end

end Work.Tubular

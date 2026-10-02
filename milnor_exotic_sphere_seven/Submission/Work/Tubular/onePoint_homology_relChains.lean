import Submission.Work.Tubular.onePoint_compl_zero
import Submission.Work.Cohomology.excision
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.homotopyInvariance

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

/-!
# (B2): the homology of `ν⁺` relative to `∞` and the relative homology of `(ν, ν∖0)`

This module assembles the comparison

  `H_{k+8}(ν⁺, {∞}) ≅ H_{k+8}(ν, ν∖0)`

of item (B2) of the tubular chapter, out of three isomorphisms:

* `H_{k+8}(ν⁺) ≅ H_{k+8}(ν⁺, A)` — the long exact sequence of the pair `(ν⁺, A)`, whose two
  neighbouring terms vanish because `A = (ν∖0) ∪ {∞}` is contractible
  (`Work.Tubular.bijective_homologyMap_onePoint_compl_zero`);
* `H_{k+8}(ν⁺, A) ≅ H_{k+8}(ν⁺∖{∞}, A∖{∞})` — **excision** of the point `{∞}`
  (`Work.Cohomology.excision`);
* `H_{k+8}(ν⁺∖{∞}, A∖{∞}) ≅ H_{k+8}(ν, ν∖0)` — the canonical identification of the complement of
  `∞` (the range of `some : ν → ν⁺`) with `ν`, which is
  `Work.Tubular.nonempty_relChains_homology_homeo`.

The main result is `Work.Tubular.nonempty_homologyIso_onePoint_relChains`.
-/

open CategoryTheory Limits
open scoped Topology

open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.Tubular

noncomputable section

open Work.Cohomology

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-! ## Relative homology is invariant under homeomorphisms of pairs -/

/-- **A homeomorphism of pairs induces an isomorphism of relative homology.**  If `e : X ≃ₜ Y`
carries `A ⊆ X` onto `B ⊆ Y`, then the induced chain map
`Work.Cohomology.relChainsMapOf X Y A B` is a quasi-isomorphism, because the two maps of pairs
`X → Y` and `A → B` are homotopy equivalences
(`Work.Cohomology.relChainsMapOf_homologyMap_isIso`). -/
theorem nonempty_relChains_homology_homeo {X Y : TopCat} (e : X ≃ₜ Y) {A : Set X} {B : Set Y}
    (hAB : ∀ x : X, x ∈ A ↔ e x ∈ B) (n : ℕ) :
    Nonempty ((relChains X A).homology n ≅ (relChains Y B).homology n) := by
  have hw : CategoryTheory.CategoryStruct.comp (subtypeIncl X A) (TopCat.ofHom e)
      = CategoryTheory.CategoryStruct.comp (TopCat.ofHom (e.subtype hAB)) (subtypeIncl Y B) := by
    ext x
    rfl
  have h1 : TopCat.Homotopy (CategoryTheory.CategoryStruct.comp (TopCat.ofHom e)
      (TopCat.ofHom (e.symm : C(↑Y, ↑X)))) (𝟙 X) := by
    have heq : (CategoryTheory.CategoryStruct.comp (TopCat.ofHom e) (TopCat.ofHom (e.symm : C(↑Y, ↑X)))
        : X ⟶ X) = 𝟙 X := by
      ext x
      exact e.symm_apply_apply x
    rw [heq]
    exact ContinuousMap.Homotopy.refl _
  have h2 : TopCat.Homotopy (CategoryTheory.CategoryStruct.comp (TopCat.ofHom (e.symm : C(↑Y, ↑X)))
      (TopCat.ofHom e)) (𝟙 Y) := by
    have heq : (CategoryTheory.CategoryStruct.comp (TopCat.ofHom (e.symm : C(↑Y, ↑X))) (TopCat.ofHom e)
        : Y ⟶ Y) = 𝟙 Y := by
      ext x
      exact e.apply_symm_apply x
    rw [heq]
    exact ContinuousMap.Homotopy.refl _
  have hf : ∀ j, IsIso (HomologicalComplex.homologyMap (chainMap ℤ X Y (TopCat.ofHom e)) j) :=
    fun j => homologyEquiv ℤ X Y (TopCat.ofHom e) (TopCat.ofHom (e.symm : C(↑Y, ↑X))) h1 h2 j
  have h1' : TopCat.Homotopy (CategoryTheory.CategoryStruct.comp (TopCat.ofHom (e.subtype hAB))
      (TopCat.ofHom ((e.subtype hAB).symm : C(↥B, ↥A)))) (𝟙 (TopCat.of A)) := by
    have heq : (CategoryTheory.CategoryStruct.comp (TopCat.ofHom (e.subtype hAB))
        (TopCat.ofHom ((e.subtype hAB).symm : C(↥B, ↥A))) : TopCat.of A ⟶ TopCat.of A) = 𝟙 (TopCat.of A) := by
      ext x
      simpa using (e.subtype hAB).symm_apply_apply x
    rw [heq]
    exact ContinuousMap.Homotopy.refl _
  have h2' : TopCat.Homotopy (CategoryTheory.CategoryStruct.comp (TopCat.ofHom ((e.subtype hAB).symm : C(↥B, ↥A)))
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
  haveI := relChainsMapOf_homologyMap_isIso A B (TopCat.ofHom e)
    (TopCat.ofHom (e.subtype hAB)) hw n hf hg
  exact ⟨asIso (HomologicalComplex.homologyMap
    (relChainsMapOf X Y A B (TopCat.ofHom e) (TopCat.ofHom (e.subtype hAB)) hw) n)⟩

/-! ## The complement of `∞` in `ν⁺` is `ν` -/

/-- **`some : X₀ → OnePoint X₀` is a homeomorphism onto the complement of `∞`**, whose inverse is
the "underlying point" of a point of `ν⁺` different from `∞`. -/
noncomputable def onePointRangeHomeo (X₀ : Type*) [TopologicalSpace X₀] :
    X₀ ≃ₜ ↥({OnePoint.infty}ᶜ : Set (OnePoint X₀)) :=
  (OnePoint.isOpenEmbedding_coe.toIsEmbedding).toHomeomorph.trans
    (Homeomorph.setCongr OnePoint.compl_infty.symm)

@[simp] theorem onePointRangeHomeo_apply {X₀ : Type*} [TopologicalSpace X₀] (x : X₀) :
    ((onePointRangeHomeo X₀ x : ↥({OnePoint.infty}ᶜ : Set (OnePoint X₀))) : OnePoint X₀)
      = OnePoint.some x := rfl

/-! ## (B2) -/

/-- **The comparison `H_{k+8}(ν⁺) ≅ H_{k+8}(ν, ν∖0)`** — item (B2) of the chapter: the homology of
the one-point compactification of the normal bundle is the relative homology of the normal bundle
with the zero section removed. -/
theorem nonempty_homologyIso_onePoint_relChains (E : EmbeddingData V (8 + k))
    (hA : ∀ n, 0 < n → CategoryTheory.Limits.IsZero
      ((singularChains ℤ (TopCat.of (onePointNonzero E))).homology n)) :
    Nonempty ((singularChains ℤ
        (TopCat.of (OnePoint (NormalTotal E)))).homology (k + 8) ≅
      (relChains (TopCat.of (NormalTotal E)) (normalNonzero E)).homology (k + 8)) := by
  have hbij := homologyMap_cokernel_pi_bijective_of_isZero
    (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E) (k + 8) (by omega)
    (hA (k + 8) (by omega)) (hA ((k + 8) - 1) (by omega))
  haveI : IsIso (HomologicalComplex.homologyMap
      (cokernel.π (inclChains (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E)))
      (k + 8)) := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  obtain ⟨e1⟩ := Nonempty.intro (asIso (HomologicalComplex.homologyMap
    (cokernel.π (inclChains (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E)))
    (k + 8)))
  have hcl : closure ({OnePoint.infty} : Set (OnePoint (NormalTotal E)))
      ⊆ interior (onePointNonzero E) := by
    rw [(OnePoint.isClosed_infty).closure_eq, (isOpen_onePointNonzero E).interior_eq]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Or.inr rfl
  obtain ⟨e2⟩ := excision (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E)
    {OnePoint.infty} hcl (k + 8)
  have hAB : ∀ y : ↥({OnePoint.infty}ᶜ : Set (OnePoint (NormalTotal E))),
      y ∈ {y : ↥({OnePoint.infty}ᶜ : Set (OnePoint (NormalTotal E))) |
          (y : OnePoint (NormalTotal E)) ∈ onePointNonzero E}
        ↔ (onePointRangeHomeo (NormalTotal E)).symm y ∈ normalNonzero E := by
    intro y
    constructor
    · intro hy
      rcases (mem_onePointNonzero.mp hy) with h | ⟨w, hw, hwy⟩
      · exact absurd h y.2
      · have h1 : OnePoint.some ((onePointRangeHomeo (NormalTotal E)).symm y)
            = (y : OnePoint (NormalTotal E)) :=
          congrArg Subtype.val ((onePointRangeHomeo (NormalTotal E)).apply_symm_apply y)
        have hwl : w = (onePointRangeHomeo (NormalTotal E)).symm y := by
          apply OnePoint.coe_injective
          rw [hwy, h1]
        rw [← hwl]
        exact hw
    · intro hy
      refine mem_onePointNonzero.mpr (Or.inr ⟨(onePointRangeHomeo (NormalTotal E)).symm y, hy, ?_⟩)
      exact congrArg Subtype.val ((onePointRangeHomeo (NormalTotal E)).apply_symm_apply y)
  obtain ⟨e3⟩ := nonempty_relChains_homology_homeo
    (X := TopCat.of ↥({OnePoint.infty}ᶜ : Set (OnePoint (NormalTotal E))))
    (Y := TopCat.of (NormalTotal E)) (onePointRangeHomeo (NormalTotal E)).symm hAB (k + 8)
  exact ⟨e1 ≪≫ e2 ≪≫ e3⟩

/-- **The comparison of (B2), unconditionally.**  The acyclicity hypothesis of
`Work.Tubular.nonempty_homologyIso_onePoint_relChains` is discharged by the contractibility of
`A = (ν ∖ 0) ∪ {∞}` (`Work.Tubular.contractibleSpace_onePointNonzero`). -/
theorem nonempty_homologyIso_onePoint_relChains' (E : EmbeddingData V (8 + k)) :
    Nonempty ((singularChains ℤ
        (TopCat.of (OnePoint (NormalTotal E)))).homology (k + 8) ≅
      (relChains (TopCat.of (NormalTotal E)) (normalNonzero E)).homology (k + 8)) :=
  nonempty_homologyIso_onePoint_relChains E
    (fun n _ => isZero_homology_onePointNonzero E n (by omega))

end

end Work.Tubular

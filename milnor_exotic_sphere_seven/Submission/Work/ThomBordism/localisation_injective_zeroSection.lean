import Mathlib
import Submission.Work.ThomBordism.chartModelClassDefs
import Submission.Work.ThomBordism.relH_zeroSection_localisation_injective
import Submission.Work.ThomBordism.FrameSigns.relKronH_natural
import Submission.Work.Cohomology.localCohomology
import Submission.Work.Tubular.exists_relKronH_eval_iso
import Submission.Work.Tubular.LocalDegree
import Submission.Work.Cohomology.cappedPairMapIso
import Submission.Work.Cohomology.pd_plumbing
import Submission.Work.ThomBordism.excludedMV
import Submission.Work.ThomBordism.exists_ne_zero_relH_normalTotal
import Submission.Work.ThomBordism.relH_localisation_injective_normalTotal

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# Injectivity of the cohomological localisation at a point of the zero section

This file proves `Work.ThomBordism.localisation_injective_zeroSection`.

Let `ν = NormalTotal E` be the normal total space of an embedding of a connected closed oriented
smooth `8`-manifold into `ℝ^{8+k}`, `A = ν ∖ 0` the complement of the zero section and
`B = ν ∖ {0_x}` the complement of a single zero-section point.  The restriction
`H^{8+k}(ν, B) → H^{8+k}(ν, A)` (the *cohomological localisation* of a class concentrated at `0_x`)
is injective.

## The proof

The groups

  `H_{8+k}(ν, ν∖0) ≅ ℤ`,   `H_{8+k}(ν, ν∖{0_x}) ≅ ℤ`,   `H^{8+k}(ν, ν∖{0_x}) ≅ ℤ`

(the Thom isomorphism in the top degree, the local homology of a point, and the local cohomology of
a point) are combined through the relative Kronecker pairing
`relKronH : H^n(X,A;ℤ) →ₗ (H_n(X,A;ℤ) →ₗ ℤ)`, which is an *isomorphism* for the pair
`(ν, ν∖{0_x})` (`Work.Tubular.exists_relKronH_eval_iso`, all homology degrees of that pair being
free) and *natural* (`Work.Tubular.relKronH_natural`).

If `α ∈ H^{8+k}(ν,ν∖{0_x})` restricts to `0`, then for every `z ∈ H_{8+k}(ν,ν∖0)`

  `⟨α, (localisation)_* z⟩ = ⟨α|_{(ν,ν∖0)}, z⟩ = 0`,

and the homology localisation `(ν,ν∖0) → (ν,ν∖{0_x})` is injective
(`Work.ThomBordism.relH_normalNonzero_localisation_injective`) with non-zero source, so it is
non-zero at some `z`; a functional on `ℤ` vanishing at a non-zero element is zero, so
`⟨α, −⟩ = 0` and hence `α = 0` by the isomorphism above.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.ThomBordism

noncomputable section

open Work.Cohomology

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-! ## Elementary facts about the normal total space -/

/-- A point of the normal total space with vanishing normal vector lies on the zero section. -/
theorem mem_range_zeroSectionNormal_of_vec_eq_zero
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {p : Work.Tubular.NormalTotal E}
    (h : (p : V.pt × Work.Tubular.Euc (8 + k)).2 = 0) :
    p ∈ Set.range (Work.Tubular.zeroSectionNormal E) := by
  refine ⟨p.1.1, ?_⟩
  apply Subtype.ext
  rw [Work.Tubular.zeroSectionNormal_apply]
  exact Prod.ext rfl h.symm

/-- **The complement of the zero section is the non-vanishing locus** of the normal norm. -/
theorem compl_range_zeroSectionNormal
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) :
    (Set.range (Work.Tubular.zeroSectionNormal E))ᶜ = Work.Tubular.normalNonzero E := by
  ext p
  rw [Set.mem_compl_iff, Work.Tubular.mem_normalNonzero, Work.Tubular.normalNorm,
    norm_ne_zero_iff]
  constructor
  · intro hp h
    exact hp (mem_range_zeroSectionNormal_of_vec_eq_zero E h)
  · intro hne hmem
    obtain ⟨y, hy⟩ := hmem
    have h2 : (p : V.pt × Work.Tubular.Euc (8 + k)).2 = 0 := by
      rw [← hy, Work.Tubular.zeroSectionNormal_apply]
    exact hne h2

/-! ## Including a subset into a set with the same complement -/

/-- The inclusion of the zero section into the complement of any point of the zero section. -/
theorem range_zeroSectionNormal_subset_compl_singleton
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    Work.Tubular.normalNonzero E
      ⊆ ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) := by
  intro p hp h
  refine (Work.Tubular.mem_normalNonzero (E := E)).mp hp ?_
  rw [h]; simp

/-! ## Chain-level bookkeeping: the identity case of `relChainsMapOf` -/

/-- The map of relative chain complexes induced by a map of pairs with identity underlying map is
the cokernel map `relCokerMap`. -/
theorem relChainsMapOf_id_eq_relCokerMap (X : TopCat) {A B : Set X} (h : A ⊆ B)
    (g : TopCat.of A ⟶ TopCat.of B)
    (w : CategoryTheory.CategoryStruct.comp (subtypeIncl X A)
          (TopCat.ofHom (ContinuousMap.id ↑X))
        = CategoryTheory.CategoryStruct.comp g (subtypeIncl X B)) :
    relChainsMapOf X X A B (TopCat.ofHom (ContinuousMap.id ↑X)) g w = relCokerMap X A B h := by
  apply (cancel_epi (cokernel.π (inclChains X A))).mp
  rw [cokernel_π_relChainsMapOf, relCokerMap_comp_π, TopCat.ofHom_id, chainMap_id',
    Category.id_comp]

/-- `relCokerMap` along an inclusion of a set into itself is the identity. -/
theorem relCokerMap_self (X : TopCat) (A : Set X) (h : A ⊆ A) :
    relCokerMap X A A h = 𝟙 (relChains X A) := by
  apply (cancel_epi (cokernel.π (inclChains X A))).mp
  rw [relCokerMap_comp_π]
  exact (Category.comp_id _).symm

/-- **Injectivity of the localisation is inherited from a set with the same elements.** -/
theorem injective_of_relCokerMap_subset_eq {X : TopCat} {A A' B : Set X} {n : ℕ}
    (hAA' : A ⊆ A') (hA'A : A' ⊆ A) (hA'B : A' ⊆ B)
    (hinj : Function.Injective
      (HomologicalComplex.homologyMap (relCokerMap X A' B hA'B) n).hom) :
    Function.Injective
      (HomologicalComplex.homologyMap (relCokerMap X A B (hAA'.trans hA'B)) n).hom := by
  have hcomp : relCokerMap X A B (hAA'.trans hA'B)
      = relCokerMap X A A' hAA' ≫ relCokerMap X A' B hA'B :=
    (relCokerMap_comp hAA' hA'B).symm
  have hpq : (HomologicalComplex.homologyMap (relCokerMap X A A' hAA') n) ≫
      (HomologicalComplex.homologyMap (relCokerMap X A' A hA'A) n)
      = 𝟙 ((relChains X A).homology n) := by
    rw [← HomologicalComplex.homologyMap_comp, relCokerMap_comp hAA' hA'A, relCokerMap_self,
      HomologicalComplex.homologyMap_id (K := relChains X A) (i := n)]
  have href : ∀ x : (relChains X A).homology n,
      (HomologicalComplex.homologyMap (relCokerMap X A' A hA'A) n).hom
        ((HomologicalComplex.homologyMap (relCokerMap X A A' hAA') n).hom x) = x := by
    intro x
    have h := congrArg (fun (k : (relChains X A).homology n ⟶ (relChains X A).homology n) =>
      k.hom x) hpq
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
      LinearMap.id_apply] at h
    exact h
  have hf : Function.Injective
      (HomologicalComplex.homologyMap (relCokerMap X A A' hAA') n).hom := by
    intro x y hxy
    have hx := href x
    have hy := href y
    rw [hxy] at hx
    exact hx.symm.trans hy
  intro a b hab
  rw [hcomp, HomologicalComplex.homologyMap_comp] at hab
  exact hf (hinj (by simpa only [ModuleCat.comp_apply] using hab))

/-! ## The algebra of a functional on `ℤ` vanishing at a non-zero element -/

/-- A `ℤ`-linear functional on a module isomorphic to `ℤ` which vanishes at a non-zero element is
zero. -/
theorem linearMap_eq_zero_of_apply_eq_zero {M : Type*} [AddCommGroup M] [Module ℤ M]
    (e : M ≃ₗ[ℤ] ℤ) (ψ : M →ₗ[ℤ] ℤ) {w : M} (hw : w ≠ 0) (h : ψ w = 0) : ψ = 0 := by
  have hgen : ∀ c : M, c = (e c) • e.symm 1 := by
    intro c
    calc c = e.symm (e c) := (e.symm_apply_apply c).symm
      _ = e.symm ((e c) • (1 : ℤ)) := by rw [smul_eq_mul, mul_one]
      _ = (e c) • e.symm 1 := by rw [map_zsmul]
  have hw' : e w ≠ 0 := fun h0 => hw (e.injective (by rw [h0, map_zero]))
  have h1 : ψ (e.symm 1) = 0 := by
    have h2 : ψ w = (e w) • ψ (e.symm 1) := by
      nth_rewrite 1 [hgen w]
      rw [map_zsmul]
    rw [h, smul_eq_mul] at h2
    exact (mul_eq_zero.mp h2.symm).resolve_left hw'
  ext c
  rw [hgen c, map_zsmul, h1, smul_zero, LinearMap.zero_apply]

/-! ## The target -/

/-- **Cohomological localisation at a point of the zero section is injective.** -/
theorem localisation_injective_zeroSection {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
    {k : ℕ} (hk : 1 ≤ k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    Function.Injective ((Work.Thom.relCohMap (ContinuousMap.id (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E)
      ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
      (fun p hp => by
        intro h
        refine (Work.Tubular.mem_normalNonzero (E := E)).mp hp ?_
        have h2 : p = Work.Tubular.zeroSectionNormal E x := by simpa using h
        rw [h2]; simp)
      ℤ (8 + k)).hom) := by
  classical
  -- the charted structure on the normal total space (this is the `ChartedSpace` instance used by
  -- `Work.Cohomology.localHomology_charted` and `Work.Cohomology.localCohomology` below)
  obtain ⟨ND⟩ := Work.ThomBordism.PontryaginThom.exists_normalData_of_immersion E.e
    (E.smooth.of_le (by simp)) E.injective_mfderiv
  obtain ⟨hChb⟩ := Work.ThomBordism.chartedSpaceTotalSpace hk (Work.Tubular.normalBundle E ND)
  letI : ChartedSpace (EuclideanSpace ℝ (Fin (8 + k)))
      (Work.Tubular.normalBundle E ND).TotalSpace := hChb
  haveI : ChartedSpace (EuclideanSpace ℝ (Fin (8 + k))) (Work.Tubular.NormalTotal E) :=
    Homeomorph.chartedSpace (Work.Tubular.eucNormalHomeomorph E ND)
  -- the local pair `(ν, ν∖{0_x})`
  have hsub : Work.Tubular.normalNonzero E
      ⊆ ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) :=
    fun p hp => by
      intro h
      refine (Work.Tubular.mem_normalNonzero (E := E)).mp hp ?_
      have h2 : p = Work.Tubular.zeroSectionNormal E x := by simpa using h
      rw [h2]; simp
  -- the local homology is free in every degree
  have hfreeB : ∀ j : ℕ, Module.Free ℤ
      ↥((relChains (TopCat.of (Work.Tubular.NormalTotal E))
        ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})).homology j) := by
    intro j
    by_cases hj : j = 8 + k
    · subst hj
      obtain ⟨e⟩ := (Work.Cohomology.localHomology_charted (8 + k) (by omega)
        (Work.Tubular.NormalTotal E) (Work.Tubular.zeroSectionNormal E x) (8 + k)).1 rfl
      exact Module.Free.of_equiv' (inferInstance : Module.Free ℤ ℤ) e.toLinearEquiv.symm
    · haveI : Subsingleton
          ↥((relChains (TopCat.of (Work.Tubular.NormalTotal E))
            ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})).homology j) :=
        ModuleCat.subsingleton_of_isZero ((Work.Cohomology.localHomology_charted (8 + k) (by omega)
          (Work.Tubular.NormalTotal E) (Work.Tubular.zeroSectionNormal E x) j).2 hj)
      exact Module.Free.of_subsingleton ℤ _
  -- the Kronecker pairing of the local pair is an isomorphism
  obtain ⟨ek, hek⟩ := Work.Tubular.exists_relKronH_eval_iso
    (TopCat.of (Work.Tubular.NormalTotal E))
    ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) (8 + k) hfreeB
  -- and the local homology is infinite cyclic
  obtain ⟨eZ⟩ := (Work.Cohomology.localHomology_charted (8 + k) (by omega)
    (Work.Tubular.NormalTotal E) (Work.Tubular.zeroSectionNormal E x) (8 + k)).1 rfl
  let eZL : ↥((relChains (TopCat.of (Work.Tubular.NormalTotal E))
      ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})).homology (8 + k))
      ≃ₗ[ℤ] ℤ := eZ.toLinearEquiv
  -- the homology localisation is injective, transported to the set `normalNonzero E`
  have hBA : ({Work.Tubular.zeroSectionNormal E x} : Set (Work.Tubular.NormalTotal E))
      ⊆ Set.range (Work.Tubular.zeroSectionNormal E) :=
    Set.singleton_subset_iff.mpr (Set.mem_range_self (f := Work.Tubular.zeroSectionNormal E) x)
  have hinj' : Function.Injective
      (HomologicalComplex.homologyMap (relCokerMap (TopCat.of (Work.Tubular.NormalTotal E))
        ((Set.range (Work.Tubular.zeroSectionNormal E))ᶜ)
        ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
        (Set.compl_subset_compl.mpr hBA)) (8 + k)).hom :=
      Work.ThomBordism.relH_localisation_injective_normalTotal (V := V) (k := k) hk E x
  have hAA' : Work.Tubular.normalNonzero E
      ⊆ ((Set.range (Work.Tubular.zeroSectionNormal E))ᶜ) := by
    rw [compl_range_zeroSectionNormal E]
  have hA'A : ((Set.range (Work.Tubular.zeroSectionNormal E))ᶜ)
      ⊆ Work.Tubular.normalNonzero E := by
    rw [compl_range_zeroSectionNormal E]
  have hA'B : ((Set.range (Work.Tubular.zeroSectionNormal E))ᶜ)
      ⊆ ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) :=
    hA'A.trans hsub
  have hinj : Function.Injective
      (HomologicalComplex.homologyMap (relCokerMap (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)
        ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
        (hAA'.trans hA'B)) (8 + k)).hom :=
    injective_of_relCokerMap_subset_eq hAA' hA'A hA'B hinj'
  -- the localisation of a non-zero global class is non-zero
  obtain ⟨z₀, hz₀⟩ := Work.ThomBordism.exists_ne_zero_relH_normalTotal (V := V) (k := k) hk E
  have hz : (HomologicalComplex.homologyMap (relCokerMap (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E)
      ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
      (hAA'.trans hA'B)) (8 + k)).hom z₀ ≠ 0 :=
    fun h => hz₀ (hinj (by rw [h, map_zero]))
  -- the naturality of the pairing along the localisation
  let gg : TopCat.of (Work.Tubular.normalNonzero E)
      ⟶ TopCat.of ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) :=
    TopCat.ofHom ⟨fun a => ⟨a.1, hsub a.2⟩,
      Continuous.subtype_mk continuous_subtype_val (fun a => hsub a.2)⟩
  let ww : CategoryTheory.CategoryStruct.comp
        (subtypeIncl (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E))
        (TopCat.ofHom (ContinuousMap.id (Work.Tubular.NormalTotal E)))
      = CategoryTheory.CategoryStruct.comp gg
        (subtypeIncl (TopCat.of (Work.Tubular.NormalTotal E))
          ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})) :=
    by apply TopCat.ext; intro a; rfl
  have hnat := Work.Tubular.relKronH_natural
    (X := TopCat.of (Work.Tubular.NormalTotal E))
    (Y := TopCat.of (Work.Tubular.NormalTotal E))
    (A := Work.Tubular.normalNonzero E)
    (B := ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}))
    (TopCat.ofHom (ContinuousMap.id (Work.Tubular.NormalTotal E))) gg hsub ww (8 + k)
  have hid := relChainsMapOf_id_eq_relCokerMap (TopCat.of (Work.Tubular.NormalTotal E))
    hsub gg ww
  have hgmap : ∀ α : Work.Thom.RelCoh ℤ (8 + k) (Work.Tubular.NormalTotal E)
        ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}),
      Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
          ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) (8 + k) α
          ((HomologicalComplex.homologyMap (relCokerMap (TopCat.of (Work.Tubular.NormalTotal E))
            (Work.Tubular.normalNonzero E)
            ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
            hsub) (8 + k)).hom z₀)
        = Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
            (Work.Tubular.normalNonzero E) (8 + k)
            ((Work.Thom.relCohMap (ContinuousMap.id (Work.Tubular.NormalTotal E))
              (Work.Tubular.normalNonzero E)
              ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
              hsub ℤ (8 + k)).hom α) z₀ := by
    intro α
    have h := hnat α z₀
    rw [hid] at h
    exact h.symm
  -- the kernel of the localisation is trivial
  have key : ∀ α : Work.Thom.RelCoh ℤ (8 + k) (Work.Tubular.NormalTotal E)
        ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}),
      (Work.Thom.relCohMap (ContinuousMap.id (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)
        ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
        hsub ℤ (8 + k)).hom α = 0 → α = 0 := by
    intro α hα
    apply ek.injective
    rw [map_zero]
    refine linearMap_eq_zero_of_apply_eq_zero eZL (ek α) hz ?_
    rw [hek]
    rw [hgmap α, hα, map_zero]
    rfl
  intro α β hab
  have hsub' : (Work.Thom.relCohMap (ContinuousMap.id (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E)
      ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
      hsub ℤ (8 + k)).hom (α - β) = 0 := by
    rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (key (α - β) hsub')

end

end Work.ThomBordism

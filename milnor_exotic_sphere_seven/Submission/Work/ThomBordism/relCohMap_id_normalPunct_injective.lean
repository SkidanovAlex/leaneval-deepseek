import Mathlib
import Submission.Work.ThomBordism.localisation_injective_zeroSection
import Submission.Work.ThomBordism.normalTotal_locH_surjective
import Submission.Work.ThomBordism.tubePointLocalisationIso
import Submission.Work.Tubular.exists_relKronH_eval_iso
import Submission.Work.ThomBordism.FrameSigns.relKronH_natural

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
# Injectivity of the cohomological localisation at a zero-section point, without hypotheses

Let `ν = NormalTotal E` be the normal total space of an embedding `E` of a closed oriented smooth
`8`-manifold into `ℝ^{8+k}`, let `A = ν ∖ 0` be the complement of the zero section and
`B = ν ∖ {0_x}` the complement of a single zero-section point, and put `n = 8 + k`.  The restriction
`H^n(ν, B) → H^n(ν, A)` is injective.

Compared with `Work.ThomBordism.localisation_injective_zeroSection` no connectivity of `V` and no
lower bound on `k` is needed:

* the relative Kronecker pairing argument only needs *surjectivity* of the homology localisation
  `H_n(ν, ν∖0) → H_n(ν, ν∖{0_x})` (whose dual is the restriction above), not injectivity, so
  `[ConnectedSpace V.pt]` is never used;
* that surjectivity is `normalTotal_locH_surjective_deg7`, which needs only `[NeZero k]` and
  `[Nonempty V.pt]`;
* for `k = 0` the embedding data is vacuous, since a closed `8`-manifold has no embedding into
  `ℝ⁸` admitting a tube chart — `false_of_embeddingData_eight`, whose connectivity hypothesis is
  used only to produce `[Nonempty V.pt]`.
-/

namespace Work.ThomBordism

open CategoryTheory

noncomputable section

/-! ## Transfer of surjectivity along an equality of the source set -/

/-- **Surjectivity version of `Work.ThomBordism.injective_of_relCokerMap_subset_eq`.**

If the localisation of the larger excluded set `A'` is surjective and `A' = A` as sets, then so is
the localisation of `A`: the map `relCokerMap X A A'` is a split epimorphism on homology. -/
theorem surjective_of_relCokerMap_subset_eq {X : TopCat} {A A' B : Set X} {n : ℕ}
    (hAA' : A ⊆ A') (hA'A : A' ⊆ A) (hA'B : A' ⊆ B)
    (hsurj : Function.Surjective
      (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap X A' B hA'B) n).hom) :
    Function.Surjective
      (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap X A B
        (hAA'.trans hA'B)) n).hom := by
  have hcomp : Work.Cohomology.relCokerMap X A B (hAA'.trans hA'B)
      = Work.Cohomology.relCokerMap X A A' hAA' ≫
        Work.Cohomology.relCokerMap X A' B hA'B :=
    (Work.Cohomology.relCokerMap_comp hAA' hA'B).symm
  have hpq : (HomologicalComplex.homologyMap
        (Work.Cohomology.relCokerMap X A' A hA'A) n) ≫
      (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap X A A' hAA') n)
      = 𝟙 ((Work.Cohomology.relChains X A').homology n) := by
    rw [← HomologicalComplex.homologyMap_comp,
      Work.Cohomology.relCokerMap_comp hA'A hAA', relCokerMap_self,
      HomologicalComplex.homologyMap_id (K := Work.Cohomology.relChains X A') (i := n)]
  have hepi : Function.Surjective
      (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap X A A' hAA') n).hom := by
    intro y
    refine ⟨(HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap X A' A hA'A) n).hom y, ?_⟩
    have h := congrArg (fun (k : (Work.Cohomology.relChains X A').homology n ⟶
        (Work.Cohomology.relChains X A').homology n) => k.hom y) hpq
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
      LinearMap.id_apply] at h
    exact h
  intro y
  obtain ⟨x', hx'⟩ := hsurj y
  obtain ⟨z, hz⟩ := hepi x'
  exact ⟨z, by
    rw [hcomp, HomologicalComplex.homologyMap_comp, ModuleCat.comp_apply, hz, hx']⟩

/-! ## The Kronecker pairing argument -/

/-- **Surjectivity of the homology localisation implies injectivity of the cohomological one.**

For `A ⊆ B ⊆ X` and `n : ℕ`, if the map `H_n(X,A) → H_n(X,B)` induced by `relCokerMap` is
surjective and the homology of the pair `(X,B)` is free in every degree, then the restriction
`H^n(X,B) → H^n(X,A)` is injective.

The relative Kronecker pairing is an isomorphism `H^n(X,B) ≅ (H_n(X,B))^*`
(`Work.Tubular.exists_relKronH_eval_iso`), and by naturality it pairs a class with the localisation
of a relative cycle; a class which restricts to `0` therefore pairs trivially with everything. -/
theorem relCohMap_id_injective_of_surjective {X : Type} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (n : ℕ)
    (hsurj : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap (TopCat.of X) A B hAB) n).hom)
    (hfree : ∀ j, Module.Free ℤ
      ↥((Work.Cohomology.relChains (TopCat.of X) B).homology j)) :
    Function.Injective (ModuleCat.Hom.hom
      (Work.Thom.relCohMap (ContinuousMap.id X) A B hAB ℤ n)) := by
  classical
  obtain ⟨ek, hek⟩ := Work.Tubular.exists_relKronH_eval_iso (TopCat.of X) B n hfree
  -- the map of pairs `(X,A) → (X,B)` and the commutation square with the identity of `X`
  let g : TopCat.of A ⟶ TopCat.of B :=
    TopCat.ofHom ⟨fun a => ⟨a.1, hAB a.2⟩,
      Continuous.subtype_mk continuous_subtype_val (fun a => hAB a.2)⟩
  have w : CategoryTheory.CategoryStruct.comp
        (Work.Cohomology.subtypeIncl (TopCat.of X) A)
        (TopCat.ofHom (ContinuousMap.id X))
      = CategoryTheory.CategoryStruct.comp g
        (Work.Cohomology.subtypeIncl (TopCat.of X) B) := by
    apply TopCat.ext
    intro a
    rfl
  intro α β hab
  have hker : (ModuleCat.Hom.hom (Work.Thom.relCohMap (ContinuousMap.id X) A B hAB ℤ n))
      (α - β) = 0 := by
    rw [map_sub, hab, sub_self]
  have hzero : ek (α - β) = 0 := by
    ext c
    obtain ⟨z, rfl⟩ := hsurj c
    -- naturality of the pairing along the localisation
    have hnat' := Work.Tubular.relKronH_natural (X := TopCat.of X) (Y := TopCat.of X)
      (A := A) (B := B) (TopCat.ofHom (ContinuousMap.id X)) g hAB w n (α - β) z
    rw [relChainsMapOf_id_eq_relCokerMap (TopCat.of X) hAB g w] at hnat'
    have h3 : Work.Tubular.relKronH (TopCat.of X) A n
        ((ModuleCat.Hom.hom (Work.Thom.relCohMap (ContinuousMap.id X) A B hAB ℤ n))
          (α - β)) z = 0 := by
      rw [hker]
      simp
    exact (hek (α - β) _).trans (hnat'.symm.trans h3)
  have hsub : α - β = 0 := ek.injective (by rw [hzero, map_zero])
  exact sub_eq_zero.mp hsub

/-! ## The surjectivity of the localisation of the normal bundle, in the form we need -/

/-- The homology localisation `H_{8+k}(ν, ν∖0) → H_{8+k}(ν, ν∖{0_x})` of the normal total space is
surjective, in the `relCokerMap` spelling with the zero section written as the range of
`zeroSectionNormal`.  This is `Work.ThomBordism.normalTotal_locH_surjective_deg7` transported across
the equal degrees `8 + k` and `7 + k + 1`. -/
theorem relCokerMap_rangeCompl_punct_surjective {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k]
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt)
    (h0 : ({Work.Tubular.zeroSectionNormal E x} : Set (Work.Tubular.NormalTotal E))
      ⊆ Set.range (Work.Tubular.zeroSectionNormal E)) :
    Function.Surjective (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap (TopCat.of (Work.Tubular.NormalTotal E))
        ((Set.range (Work.Tubular.zeroSectionNormal E))ᶜ)
        ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
        (Set.compl_subset_compl.mpr h0)) (8 + k)).hom := by
  haveI : Nonempty V.pt := ⟨x⟩
  have h7 := Work.ThomBordism.normalTotal_locH_surjective_deg7 (V := V) (k := k) E x h0
  show Function.Surjective (Work.Orient.resRelH (TopCat.of (Work.Tubular.NormalTotal E))
    (8 + k) h0)
  suffices ∀ (N : ℕ), N = 7 + k + 1 → Function.Surjective
      (Work.Orient.resRelH (TopCat.of (Work.Tubular.NormalTotal E)) N h0) by
    exact this (8 + k) (by omega)
  intro N hN
  subst hN
  exact h7

/-! ## The case `k = 0` is vacuous -/

/-- **No closed embedding of a compact `8`-manifold into `ℝ⁸` admits a tube chart.**

This is `Work.ThomBordism.false_of_embeddingData_eight` with the (unnecessary) hypothesis
`[ConnectedSpace V.pt]` weakened to `[Nonempty V.pt]`: the connectedness there is used only to
produce a point of `V`. -/
theorem false_of_embeddingData_eight' {V : Work.ThomBordism.Man8} [Nonempty V.pt] {ε : ℝ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V 8) (C : Work.Tubular.TubeChart E ε) :
    False := by
  have hvec : ∀ p : Work.Tubular.NormalTotal E, (p : V.pt × Work.Tubular.Euc 8).2 = 0 := by
    intro p
    have hfr : Module.finrank ℝ ↥(Work.Tubular.normalSpace E p.1.1) = 0 := by
      have h := Work.Tubular.finrank_normalSpace E p.1.1
      simpa using h
    have hbot : Work.Tubular.normalSpace E p.1.1 = ⊥ :=
      (Submodule.finrank_eq_zero).mp hfr
    have hmem : (p : V.pt × Work.Tubular.Euc 8).2 ∈ Work.Tubular.normalSpace E p.1.1 := p.2
    rw [hbot] at hmem
    simpa using hmem
  have hnorm : ∀ p : Work.Tubular.NormalTotal E, Work.Tubular.normalNorm E p = 0 := by
    intro p
    simp [Work.Tubular.normalNorm, hvec p]
  have hrange : Work.Tubular.openTubeSet E ε = Set.range E.e := by
    rw [Work.Tubular.openTubeSet]
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p.1.1, ?_⟩
      rw [Work.Tubular.tubeMap, hvec p, add_zero]
    · rintro ⟨x, rfl⟩
      refine ⟨Work.Tubular.zeroSectionNormal (k := 0) E x, ?_, ?_⟩
      · show Work.Tubular.normalNorm E (Work.Tubular.zeroSectionNormal (k := 0) E x) < ε
        rw [hnorm]; exact C.eps_pos
      · rw [Work.Tubular.tubeMap, Work.Tubular.zeroSectionNormal_apply]
        simp
  have hopen : IsOpen (Set.range E.e) := hrange ▸ C.isOpen_openTube
  have hclosed : IsClosed (Set.range E.e) := E.closedEmbedding.isClosed_range
  have hne : (Set.range E.e).Nonempty :=
    ⟨E.e (Classical.choice (inferInstance : Nonempty V.pt)), _, rfl⟩
  have huniv : Set.range E.e = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ hne
  have hcomp : IsCompact (Set.univ : Set (Work.Tubular.Euc 8)) := by
    rw [← huniv]
    exact isCompact_range E.smooth.continuous
  exact not_compactSpace_iff.mpr (inferInstance : NoncompactSpace (Work.Tubular.Euc 8))
    (isCompact_univ_iff.mp hcomp)

/-! ## The target -/

theorem relCohMap_id_normalPunct_injective {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    Function.Injective (ModuleCat.Hom.hom (Work.Thom.relCohMap
      (ContinuousMap.id (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E)
      ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x} : Set (Work.Tubular.NormalTotal E))
      (fun p hp => by
        intro h
        refine (Work.Tubular.mem_normalNonzero (E := E)).mp hp ?_
        have h2 : p = Work.Tubular.zeroSectionNormal E x := by simpa using h
        rw [h2]; simp) ℤ (8 + k))) := by
  rcases k with _ | m
  · -- there is no embedding of a closed `8`-manifold into `ℝ⁸` admitting a tube chart
    haveI : Nonempty V.pt := ⟨x⟩
    obtain ⟨ε, _hε, ⟨C⟩⟩ := Work.Tubular.hasTubularNeighbourhood E
    exact (false_of_embeddingData_eight' E C).elim
  · -- for `k ≥ 1` the localisation of the homology of the normal bundle is surjective
    haveI : NeZero (m + 1) := inferInstance
    have hk : 1 ≤ m + 1 := Nat.le_add_left 1 m
    classical
    obtain ⟨ND⟩ := Work.ThomBordism.PontryaginThom.exists_normalData_of_immersion E.e
      (E.smooth.of_le (by simp)) E.injective_mfderiv
    obtain ⟨hChb⟩ := Work.ThomBordism.chartedSpaceTotalSpace hk (Work.Tubular.normalBundle E ND)
    letI : ChartedSpace (EuclideanSpace ℝ (Fin (8 + (m + 1))))
        (Work.Tubular.normalBundle E ND).TotalSpace := hChb
    haveI : ChartedSpace (EuclideanSpace ℝ (Fin (8 + (m + 1))))
        (Work.Tubular.NormalTotal E) :=
      Homeomorph.chartedSpace (Work.Tubular.eucNormalHomeomorph E ND)
    -- the homology of the pair `(ν, B)` is free in every degree
    have hfreeB : ∀ j : ℕ, Module.Free ℤ
        ↥((Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
          ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})).homology j) := by
      intro j
      by_cases hj : j = 8 + (m + 1)
      · subst hj
        obtain ⟨e⟩ := (Work.Cohomology.localHomology_charted (8 + (m + 1)) (by omega)
          (Work.Tubular.NormalTotal E) (Work.Tubular.zeroSectionNormal E x) (8 + (m + 1))).1 rfl
        exact Module.Free.of_equiv' (inferInstance : Module.Free ℤ ℤ) e.toLinearEquiv.symm
      · haveI : Subsingleton
            ↥((Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
              ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})).homology j) :=
          ModuleCat.subsingleton_of_isZero ((Work.Cohomology.localHomology_charted (8 + (m + 1))
            (by omega) (Work.Tubular.NormalTotal E) (Work.Tubular.zeroSectionNormal E x) j).2 hj)
        exact Module.Free.of_subsingleton ℤ _
    -- the subsets
    have hsub0 : ({Work.Tubular.zeroSectionNormal E x} : Set (Work.Tubular.NormalTotal E))
        ⊆ Set.range (Work.Tubular.zeroSectionNormal E) :=
      Set.singleton_subset_iff.mpr (Set.mem_range_self (f := Work.Tubular.zeroSectionNormal E) x)
    have hA'B : ((Set.range (Work.Tubular.zeroSectionNormal E))ᶜ :
          Set (Work.Tubular.NormalTotal E))
        ⊆ ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) :=
      Set.compl_subset_compl.mpr hsub0
    have hAA' : Work.Tubular.normalNonzero E
        ⊆ ((Set.range (Work.Tubular.zeroSectionNormal E))ᶜ : Set (Work.Tubular.NormalTotal E)) := by
      rw [compl_range_zeroSectionNormal E]
    have hA'A : ((Set.range (Work.Tubular.zeroSectionNormal E))ᶜ :
          Set (Work.Tubular.NormalTotal E))
        ⊆ Work.Tubular.normalNonzero E := by
      rw [compl_range_zeroSectionNormal E]
    -- the surjectivity of the localisation, first for the complement of the zero section
    have hsurj0 : Function.Surjective (HomologicalComplex.homologyMap
        (Work.Cohomology.relCokerMap (TopCat.of (Work.Tubular.NormalTotal E))
          ((Set.range (Work.Tubular.zeroSectionNormal E))ᶜ)
          ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
          (Set.compl_subset_compl.mpr hsub0)) (8 + (m + 1))).hom :=
      relCokerMap_rangeCompl_punct_surjective (V := V) (k := m + 1) E x hsub0
    -- and then for the non-zero locus, which is the same set
    have hsurj : Function.Surjective (HomologicalComplex.homologyMap
        (Work.Cohomology.relCokerMap (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E)
          ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})
          (hAA'.trans hA'B)) (8 + (m + 1))).hom :=
      surjective_of_relCokerMap_subset_eq hAA' hA'A hA'B hsurj0
    -- the Kronecker pairing argument
    have key : Function.Injective (ModuleCat.Hom.hom (Work.Thom.relCohMap
        (ContinuousMap.id (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)
        ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}
          : Set (Work.Tubular.NormalTotal E))
        (hAA'.trans hA'B) ℤ (8 + (m + 1)))) :=
      relCohMap_id_injective_of_surjective (hAA'.trans hA'B) (8 + (m + 1)) hsurj hfreeB
    -- the two proofs of the inclusion differ only as proofs of a proposition
    exact key

end

end Work.ThomBordism

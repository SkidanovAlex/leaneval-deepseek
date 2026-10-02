import Mathlib
import Submission.Work.ThomBordism.Interface
import Submission.Work.Orient.Boundary.BoundaryOrientation
import Submission.Work.Orient.Boundary.injective_localisation_of_halfBallInterior
import Submission.Work.Orient.Boundary.tripleConnectingMap_surjective_of_isRelFundClass
import Submission.Work.Orient.Boundary.TripleSetup
import Submission.Work.Orient.Bridge
import Submission.Work.Orient.Boundary.RelChainsBridge
import Submission.Work.Orient.Boundary.LocalClassConstantOnBall
import Submission.Work.ThomBordism.halfBallInteriorUnionPoint_allDeg
import Submission.Work.ThomBordism.locClass_hPairDelta_eq_tripleDelta

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.ThomBordism

noncomputable section

/-- The homology map of an isomorphism of chain complexes is an isomorphism. -/
theorem isIso_homologyMap_of_isIso {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Limits.HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex C c} (φ : K ⟶ L) [CategoryTheory.IsIso φ] (i : ι)
    [K.HasHomology i] [L.HasHomology i] :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap φ i) := by
  have h : CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (CategoryTheory.asIso φ).hom i) :=
    CategoryTheory.Iso.isIso_hom (HomologicalComplex.homologyMapIso (CategoryTheory.asIso φ) i)
  simpa only [CategoryTheory.asIso_hom] using h

/-- A bijective `ℤ`-linear map preserves the property of an element of generating its module. -/
theorem span_singleton_eq_top_iff_of_bijective {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) (hf : Function.Bijective f) (a : M) :
    Submodule.span ℤ (Set.singleton (f a)) = ⊤ ↔ Submodule.span ℤ (Set.singleton a) = ⊤ := by
  have hspan : Submodule.span ℤ (Set.singleton (f a))
      = Submodule.map f (Submodule.span ℤ (Set.singleton a)) := by
    rw [Submodule.map_span]
    congr 1
    ext x
    constructor
    · intro hx
      exact ⟨a, Set.mem_singleton_iff.mpr rfl, (Set.mem_singleton_iff.mp hx).symm⟩
    · rintro ⟨y, hy, rfl⟩
      rw [Set.mem_singleton_iff.mp hy]
      exact Set.mem_singleton_iff.mpr rfl
  rw [hspan]
  constructor
  · intro h
    rw [Submodule.eq_top_iff']
    intro b
    have hmem : f b ∈ Submodule.map f (Submodule.span ℤ (Set.singleton a)) := by
      rw [h]; exact Submodule.mem_top
    obtain ⟨b', hb', heq⟩ := Submodule.mem_map.mp hmem
    rw [hf.1 heq] at hb'
    exact hb'
  · intro h
    rw [h, Submodule.map_top, LinearMap.range_eq_top]
    exact hf.2

/-- A bijective `ℤ`-linear map vanishes on exactly the elements on which its value vanishes. -/
theorem eq_zero_iff_of_bijective {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) (hf : Function.Bijective f) (a : M) :
    f a = 0 ↔ a = 0 :=
  ⟨fun h => hf.1 (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

/-- **The statement in the vocabulary of the triple machinery.**  This is
`Work.ThomBordism.piecesBound_locGen_iff` with `(modelWithCornersEuclideanHalfSpace 9).boundary W`
written as `Work.Orient.Boundary.bdrySetW 8 (TopCat.of W)` and `relChainsInclPunct` written as
`Work.Orient.relPunct`; the two are definitionally the same. -/
theorem piecesBound_locGen_iff_aux
    {W : Type} [TopologicalSpace W] [T2Space W] [CompactSpace W]
    [ChartedSpace (EuclideanHalfSpace 9) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 W]
    (w₀ : (Work.Cohomology.relChains (TopCat.of W)
      (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W))).homology 9)
    (hw₀ : Work.Orient.IsRelFundClass (TopCat.of W) 9
      (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W)) w₀)
    (y : W) (hy : y ∈ Work.Orient.Boundary.bdrySetW 8 (TopCat.of W))
    (r : ℝ) (hr : 0 < r) (hgood : Work.Orient.halfBallGood 9 (TopCat.of W) y r)
    (x : W) (hxK : x ∈ Work.Orient.halfBallPiece 9 (TopCat.of W) y r)
    (hx : x ∉ Work.Orient.Boundary.bdrySetW 8 (TopCat.of W))
    (w : (Work.Cohomology.relChains (TopCat.of W)
      (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W))).homology 9) :
    ((Submodule.span ℤ {(HomologicalComplex.homologyMap
        (Work.Orient.relPunct (TopCat.of W)
          (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W)) x hx) 9 w)} = ⊤) ↔
      (Submodule.span ℤ {(Work.Orient.locClass
        (TopCat.of ↥(Work.Orient.Boundary.bdrySetW 8 (TopCat.of W))) 8
        ((Work.Cohomology.hPairδ (TopCat.of W)
          (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W)) 8).hom w) ⟨y, hy⟩)} = ⊤)) ∧
    ((HomologicalComplex.homologyMap
        (Work.Orient.relPunct (TopCat.of W)
          (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W)) x hx) 9 w = 0) ↔
      (Work.Orient.locClass
        (TopCat.of ↥(Work.Orient.Boundary.bdrySetW 8 (TopCat.of W))) 8
        ((Work.Cohomology.hPairδ (TopCat.of W)
          (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W)) 8).hom w) ⟨y, hy⟩ = 0)) := by
  classical
  -- ### the sets
  have hBdB : Work.Orient.Boundary.bdrySetW 8 (TopCat.of W)
      ⊆ Work.Orient.Boundary.bigB 8 (TopCat.of W) y r :=
    Work.Orient.Boundary.bdrySetW_sub_bigB 8 (TopCat.of W) y r
  have hBAB : Work.Orient.Boundary.bigA 8 (TopCat.of W) y r
      ⊆ Work.Orient.Boundary.bigB 8 (TopCat.of W) y r :=
    Work.Orient.Boundary.bigA_sub_bigB 8 (TopCat.of W) y r
  have hMinBd : Work.Orient.Boundary.bdryMinus 8 (TopCat.of W) y
      ⊆ Work.Orient.Boundary.bdrySetW 8 (TopCat.of W) :=
    Work.Orient.Boundary.bdryMinus_sub_bdrySetW 8 (TopCat.of W) y
  have hMinBA : Work.Orient.Boundary.bdryMinus 8 (TopCat.of W) y
      ⊆ Work.Orient.Boundary.bigA 8 (TopCat.of W) y r :=
    Work.Orient.Boundary.bdryMinus_sub_bigA 8 (TopCat.of W) y r
  have hxBB : x ∉ Work.Orient.Boundary.bigB 8 (TopCat.of W) y r := by
    have h : Work.Orient.Boundary.bigB 8 (TopCat.of W) y r
        = ((Work.Orient.halfBallPiece 9 (TopCat.of W) y r) ∩
            (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W))ᶜ)ᶜ := rfl
    rw [h]
    exact fun hh => hh ⟨hxK, hx⟩
  have hBBx : Work.Orient.Boundary.bigB 8 (TopCat.of W) y r ⊆ {z : W | z ≠ x} :=
    fun z hz hzx => hxBB (hzx ▸ hz)
  -- ### the chain-level factorisation of the localisation at `x`
  have hLfac : Work.Orient.relPunct (TopCat.of W)
        (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W)) x hx
      = Work.Orient.relChainsIncl (TopCat.of W) hBdB
        ≫ Work.Orient.relChainsIncl (TopCat.of W) hBBx := by
    rw [Work.Orient.Boundary.relPunct_eq_relChainsIncl,
      ← Work.Orient.Boundary.relChainsIncl_comp hBdB hBBx]
  -- ### the maps in homology
  set ρL : (↑(HomologicalComplex.homology (Work.Cohomology.relChains (TopCat.of W)
        (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W))) 9)) →ₗ[ℤ]
      (↑(HomologicalComplex.homology (Work.Cohomology.relChains (TopCat.of W)
        (Work.Orient.Boundary.bigB 8 (TopCat.of W) y r)) 9)) :=
    (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap (TopCat.of W)
        (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W))
        (Work.Orient.Boundary.bigB 8 (TopCat.of W) y r) hBdB) 9).hom with hρL
  set jL : (↑(HomologicalComplex.homology (Work.Cohomology.relChains (TopCat.of W)
        (Work.Orient.Boundary.bigB 8 (TopCat.of W) y r)) 9)) →ₗ[ℤ]
      (↑(HomologicalComplex.homology (Work.Cohomology.relChains (TopCat.of W)
        {z : W | z ≠ x}) 9)) :=
    (HomologicalComplex.homologyMap
      (Work.Orient.relChainsIncl (TopCat.of W) hBBx) 9).hom with hjL
  set LL : (↑(HomologicalComplex.homology (Work.Cohomology.relChains (TopCat.of W)
        (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W))) 9)) →ₗ[ℤ]
      (↑(HomologicalComplex.homology (Work.Cohomology.relChains (TopCat.of W)
        {z : W | z ≠ x}) 9)) :=
    (HomologicalComplex.homologyMap
      (Work.Orient.relPunct (TopCat.of W)
        (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W)) x hx) 9).hom with hLL
  have hLsplit : LL = jL.comp ρL := by
    rw [hLL, hρL, hjL]
    ext a
    rw [LinearMap.comp_apply]
    rw [hLfac, show Work.Orient.relChainsIncl (TopCat.of W) hBdB
        = Work.Cohomology.relCokerMap (TopCat.of W)
            (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W))
            (Work.Orient.Boundary.bigB 8 (TopCat.of W) y r) hBdB from
      Work.Orient.Boundary.relChainsIncl_eq_relCokerMap (TopCat.of W) hBdB,
      HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  -- ### `jL` is bijective
  have hjL_inj : Function.Injective jL := by
    rw [hjL]
    have hxP : x ∈ Work.Orient.halfBallPiece 9 (TopCat.of W) y r ∩
        {z : W | z ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W} := ⟨hxK, hx⟩
    have hinj := Work.Orient.Boundary.injective_localisation_of_halfBallInterior 8 (TopCat.of W)
      y hy r hr hgood x hxP
    rw [Work.Orient.resRelH_eq_homologyMap_relChainsIncl] at hinj
    have hsame : Work.Orient.relChainsIncl (TopCat.of W)
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hxP))
        = Work.Orient.relChainsIncl (TopCat.of W) hBBx :=
      Work.Orient.Boundary.relChainsIncl_congr_h _ _
    rw [hsame] at hinj
    exact hinj
  have hLL_surj : Function.Surjective LL := by
    rw [hLL]
    have hspan : Submodule.span ℤ
        ({((HomologicalComplex.homologyMap (Work.Orient.relPunct (TopCat.of W)
          (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W)) x hx) 9).hom w₀)} : Set _) = ⊤ :=
      hw₀ x hx
    have hmap : Submodule.map (HomologicalComplex.homologyMap (Work.Orient.relPunct (TopCat.of W)
          (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W)) x hx) 9).hom
        (Submodule.span ℤ ({w₀} : Set _)) = ⊤ := by
      rw [Submodule.map_span, Set.image_singleton]
      exact hspan
    have hle : (⊤ : Submodule ℤ _) ≤ LinearMap.range
        (HomologicalComplex.homologyMap (Work.Orient.relPunct (TopCat.of W)
          (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W)) x hx) 9).hom := by
      rw [← hmap]
      rintro _ ⟨z, -, rfl⟩
      exact ⟨z, rfl⟩
    intro c
    have hmem : c ∈ LinearMap.range
        (HomologicalComplex.homologyMap (Work.Orient.relPunct (TopCat.of W)
          (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W)) x hx) 9).hom := hle trivial
    exact hmem
  have hρL_surj : Function.Surjective ρL := by
    intro a
    obtain ⟨d, hd⟩ := hLL_surj (jL a)
    rw [hLsplit, LinearMap.comp_apply] at hd
    exact ⟨d, hjL_inj hd⟩
  have hjL_surj : Function.Surjective jL := by
    intro b
    obtain ⟨c, hc⟩ := hLL_surj b
    rw [hLsplit, LinearMap.comp_apply] at hc
    exact ⟨ρL c, hc⟩
  have hjL_bij : Function.Bijective jL := ⟨hjL_inj, hjL_surj⟩
  -- ### the connecting maps of the two triples
  set Δy : (↑(HomologicalComplex.homology (Work.Cohomology.relChains (TopCat.of W)
        (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W))) 9)) →ₗ[ℤ]
      (↑((Work.Cohomology.tripleShort (TopCat.of W)
        (Work.Orient.Boundary.bdryMinus 8 (TopCat.of W) y)
        (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W)) hMinBd).X₁.homology 8)) :=
    ((Work.Cohomology.relChains_triple_shortExact (TopCat.of W)
      (Work.Orient.Boundary.bdryMinus 8 (TopCat.of W) y)
      (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W)) hMinBd).δ 9 8
        (by simp [ComplexShape.down])).hom with hΔy
  set eL : (↑((Work.Cohomology.tripleShort (TopCat.of W)
        (Work.Orient.Boundary.bdryMinus 8 (TopCat.of W) y)
        (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W)) hMinBd).X₁.homology 8)) →ₗ[ℤ]
      (↑((Work.Cohomology.tripleShort (TopCat.of W)
        (Work.Orient.Boundary.bigA 8 (TopCat.of W) y r)
        (Work.Orient.Boundary.bigB 8 (TopCat.of W) y r) hBAB).X₁.homology 8)) :=
    (HomologicalComplex.homologyMap
      (Work.Orient.Boundary.tripleMap (TopCat.of W) hMinBd hBAB hMinBA hBdB).τ₁ 8).hom with heL
  set δ2L : (↑(HomologicalComplex.homology (Work.Cohomology.relChains (TopCat.of W)
        (Work.Orient.Boundary.bigB 8 (TopCat.of W) y r)) 9)) →ₗ[ℤ]
      (↑((Work.Cohomology.tripleShort (TopCat.of W)
        (Work.Orient.Boundary.bigA 8 (TopCat.of W) y r)
        (Work.Orient.Boundary.bigB 8 (TopCat.of W) y r) hBAB).X₁.homology 8)) :=
    ((Work.Cohomology.relChains_triple_shortExact (TopCat.of W)
      (Work.Orient.Boundary.bigA 8 (TopCat.of W) y r)
      (Work.Orient.Boundary.bigB 8 (TopCat.of W) y r) hBAB).δ 9 8
        (by simp [ComplexShape.down])).hom with hδ2L
  set ΦL : (↑((Work.Cohomology.tripleShort (TopCat.of W)
        (Work.Orient.Boundary.bdryMinus 8 (TopCat.of W) y)
        (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W)) hMinBd).X₁.homology 8)) →ₗ[ℤ]
      Work.Orient.LocH (TopCat.of ↥(Work.Orient.Boundary.bdrySetW 8 (TopCat.of W))) 8 ⟨y, hy⟩ :=
    (HomologicalComplex.homologyMap (Work.Orient.Boundary.diffCokerMap (TopCat.of W)
      (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W)) y hy hMinBd) 8).hom with hΦL
  -- ### the square of the connecting maps
  have hsquare : ∀ a, eL (Δy a) = δ2L (ρL a) := by
    intro a
    rw [heL, hΔy, hδ2L, hρL]
    have hnat := Work.Orient.Boundary.tripleMap_delta_naturality (TopCat.of W) hMinBd hBAB
      hMinBA hBdB 8
    have h := ConcreteCategory.congr_hom hnat a
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at h
    exact h
  have hδ2surj : Function.Surjective δ2L := by
    rw [hδ2L]
    exact Work.Orient.Boundary.triple_δ_surjective_of_isZero 8 (TopCat.of W) y hy r hr hgood
  have heL_inj : Function.Injective eL := by
    rw [heL]
    exact Work.Orient.Boundary.tripleConnecting_input₁ 8 (TopCat.of W) y hy r hr hgood
  have heL_surj : Function.Surjective eL := by
    intro b
    obtain ⟨a, ha⟩ := hδ2surj b
    obtain ⟨c, hc⟩ := hρL_surj a
    exact ⟨Δy c, by rw [hsquare c, hc, ha]⟩
  have heL_bij : Function.Bijective eL := ⟨heL_inj, heL_surj⟩
  -- ### the D side
  have hDfac : Work.Orient.locClass
        (TopCat.of ↥(Work.Orient.Boundary.bdrySetW 8 (TopCat.of W))) 8
        ((Work.Cohomology.hPairδ (TopCat.of W)
          (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W)) 8).hom w) ⟨y, hy⟩ = ΦL (Δy w) := by
    rw [hΦL, hΔy]
    exact Work.ThomBordism.locClass_hPairDelta_eq_tripleDelta 8 (TopCat.of W) w y hy
  have hΦL_bij : Function.Bijective ΦL := by
    rw [hΦL]
    haveI h1 : CategoryTheory.IsIso (Work.Orient.Boundary.diffCokerMap (TopCat.of W)
        (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W)) y hy hMinBd) :=
      Work.Orient.Boundary.diffCokerMap_isIso (TopCat.of W)
        (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W)) y hy hMinBd
    have h2 := isIso_homologyMap_of_isIso (Work.Orient.Boundary.diffCokerMap (TopCat.of W)
      (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W)) y hy hMinBd) 8
    exact (ConcreteCategory.isIso_iff_bijective _).mp h2
  -- ### the crux: `δ2L` is injective
  have hδ2L_inj : Function.Injective δ2L := by
    rw [hδ2L]
    have hcrux : CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains (TopCat.of W)
        (Work.Orient.Boundary.bigA 8 (TopCat.of W) y r)).homology 9) := by
      rw [Work.Orient.Boundary.bigA_eq]
      exact Work.ThomBordism.halfBallInteriorUnionPoint_allDeg 8 (TopCat.of W) y hy r hr hgood 9
    have hexact := (Work.Cohomology.relChains_triple_shortExact (TopCat.of W)
      (Work.Orient.Boundary.bigA 8 (TopCat.of W) y r)
      (Work.Orient.Boundary.bigB 8 (TopCat.of W) y r) hBAB).homology_exact₃ 9 8
        (by simp [ComplexShape.down])
    have hg0 : HomologicalComplex.homologyMap (Work.Cohomology.tripleShort (TopCat.of W)
        (Work.Orient.Boundary.bigA 8 (TopCat.of W) y r)
        (Work.Orient.Boundary.bigB 8 (TopCat.of W) y r) hBAB).g 9 = 0 :=
      CategoryTheory.Limits.IsZero.eq_zero_of_src hcrux _
    have hr : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (Work.Cohomology.tripleShort
        (TopCat.of W) (Work.Orient.Boundary.bigA 8 (TopCat.of W) y r)
        (Work.Orient.Boundary.bigB 8 (TopCat.of W) y r) hBAB).g 9)).range =
        (ModuleCat.Hom.hom (((Work.Cohomology.relChains_triple_shortExact (TopCat.of W)
          (Work.Orient.Boundary.bigA 8 (TopCat.of W) y r)
          (Work.Orient.Boundary.bigB 8 (TopCat.of W) y r) hBAB).δ 9 8
            (by simp [ComplexShape.down])))).ker :=
      CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker hexact
    rw [hg0, ModuleCat.hom_zero, LinearMap.range_zero] at hr
    exact LinearMap.ker_eq_bot.mp hr.symm
  have hδ2L_bij : Function.Bijective δ2L := ⟨hδ2L_inj, hδ2surj⟩
  -- ### assemble: `D = ΨL ∘ ρL` with `ΨL` bijective
  set eEquiv : (↑((Work.Cohomology.tripleShort (TopCat.of W)
        (Work.Orient.Boundary.bdryMinus 8 (TopCat.of W) y)
        (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W)) hMinBd).X₁.homology 8)) ≃ₗ[ℤ]
      (↑((Work.Cohomology.tripleShort (TopCat.of W)
        (Work.Orient.Boundary.bigA 8 (TopCat.of W) y r)
        (Work.Orient.Boundary.bigB 8 (TopCat.of W) y r) hBAB).X₁.homology 8)) :=
    LinearEquiv.ofBijective eL heL_bij with heE
  set ΨL : (↑(HomologicalComplex.homology (Work.Cohomology.relChains (TopCat.of W)
        (Work.Orient.Boundary.bigB 8 (TopCat.of W) y r)) 9)) →ₗ[ℤ]
      Work.Orient.LocH (TopCat.of ↥(Work.Orient.Boundary.bdrySetW 8 (TopCat.of W))) 8 ⟨y, hy⟩ :=
    ΦL.comp (eEquiv.symm.toLinearMap.comp δ2L) with hΨL
  have hΔfac : ∀ a, Δy a = eEquiv.symm (δ2L (ρL a)) := by
    intro a
    refine (eEquiv.toEquiv.eq_symm_apply).mpr ?_
    exact hsquare a
  have hDLfac : Work.Orient.locClass
        (TopCat.of ↥(Work.Orient.Boundary.bdrySetW 8 (TopCat.of W))) 8
        ((Work.Cohomology.hPairδ (TopCat.of W)
          (Work.Orient.Boundary.bdrySetW 8 (TopCat.of W)) 8).hom w) ⟨y, hy⟩ = ΨL (ρL w) := by
    rw [hDfac, hΔfac w, hΨL]
    rfl
  have hΨL_bij : Function.Bijective ΨL := by
    rw [hΨL]
    refine ⟨fun a b hab => ?_, fun c => ?_⟩
    · have h1 : eEquiv.symm (δ2L a) = eEquiv.symm (δ2L b) := hΦL_bij.1 hab
      exact hδ2L_inj (eEquiv.symm.injective h1)
    · obtain ⟨d, hd⟩ := hΦL_bij.2 c
      obtain ⟨a, ha⟩ := hδ2L_bij.2 (eEquiv d)
      refine ⟨a, ?_⟩
      show ΦL (eEquiv.symm (δ2L a)) = c
      rw [ha, LinearEquiv.symm_apply_apply, hd]
  -- ### conclusion
  have hg1 : (Submodule.span ℤ ({LL w} : Set _) = ⊤) ↔
      (Submodule.span ℤ ({ρL w} : Set _) = ⊤) := by
    rw [hLsplit, LinearMap.comp_apply]
    exact span_singleton_eq_top_iff_of_bijective jL hjL_bij (ρL w)
  have hg2 : (Submodule.span ℤ ({ΨL (ρL w)} : Set _) = ⊤) ↔
      (Submodule.span ℤ ({ρL w} : Set _) = ⊤) :=
    span_singleton_eq_top_iff_of_bijective ΨL hΨL_bij (ρL w)
  have hz1 : (LL w = 0) ↔ (ρL w = 0) := by
    rw [hLsplit, LinearMap.comp_apply]
    exact eq_zero_iff_of_bijective jL hjL_bij (ρL w)
  have hz2 : (ΨL (ρL w) = 0) ↔ (ρL w = 0) := eq_zero_iff_of_bijective ΨL hΨL_bij (ρL w)
  rw [hDLfac]
  refine ⟨?_, ?_⟩
  · exact hg1.trans hg2.symm
  · exact hz1.trans hz2.symm

theorem piecesBound_locGen_iff
    {W : Type} [TopologicalSpace W] [T2Space W] [CompactSpace W]
    [ChartedSpace (EuclideanHalfSpace 9) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 W]
    (w₀ : (Work.Cohomology.relChains (TopCat.of W)
      ((modelWithCornersEuclideanHalfSpace 9).boundary W)).homology 9)
    (hw₀ : Work.Orient.IsRelFundClass (TopCat.of W) 9
      ((modelWithCornersEuclideanHalfSpace 9).boundary W) w₀)
    (y : W) (hy : y ∈ (modelWithCornersEuclideanHalfSpace 9).boundary W)
    (r : ℝ) (hr : 0 < r) (hgood : Work.Orient.halfBallGood 9 (TopCat.of W) y r)
    (x : W) (hxK : x ∈ Work.Orient.halfBallPiece 9 (TopCat.of W) y r)
    (hx : x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary W)
    (w : (Work.Cohomology.relChains (TopCat.of W)
      ((modelWithCornersEuclideanHalfSpace 9).boundary W)).homology 9) :
    ((Submodule.span ℤ {(HomologicalComplex.homologyMap
        (Work.ThomBordism.relChainsInclPunct (TopCat.of W)
          ((modelWithCornersEuclideanHalfSpace 9).boundary W) x hx) 9 w)} = ⊤) ↔
      (Submodule.span ℤ {(Work.Orient.locClass
        (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary W)) 8
        ((Work.Cohomology.hPairδ (TopCat.of W)
          ((modelWithCornersEuclideanHalfSpace 9).boundary W) 8).hom w) ⟨y, hy⟩)} = ⊤)) ∧
    ((HomologicalComplex.homologyMap
        (Work.ThomBordism.relChainsInclPunct (TopCat.of W)
          ((modelWithCornersEuclideanHalfSpace 9).boundary W) x hx) 9 w = 0) ↔
      (Work.Orient.locClass
        (TopCat.of ↥((modelWithCornersEuclideanHalfSpace 9).boundary W)) 8
        ((Work.Cohomology.hPairδ (TopCat.of W)
          ((modelWithCornersEuclideanHalfSpace 9).boundary W) 8).hom w) ⟨y, hy⟩ = 0)) := by
  refine (Work.ThomBordism.piecesBound_locGen_iff_aux w₀ hw₀ y hy r hr hgood x hxK hx w).imp ?_ ?_
  · intro h
    rwa [Work.Orient.relPunct_eq_relChainsInclPunct] at h
  · intro h
    rwa [Work.Orient.relPunct_eq_relChainsInclPunct] at h

end

end Work.ThomBordism

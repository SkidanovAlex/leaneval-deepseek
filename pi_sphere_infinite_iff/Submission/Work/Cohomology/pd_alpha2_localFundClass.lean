import Mathlib
import Submission.Work.Cohomology.pd_glue3
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.pd_hatcher_W
import Submission.Work.Cohomology.chainRetract_mem_range_inclChains
import Submission.Work.Cohomology.pd_goodD_incl

/-!
# The middle summand of the Hatcher decomposition represents the local fundamental class

Given a relative cycle `ζ` of the pair `(U ∪ V, (U ∪ V)∖(K ∩ L))` whose underlying chain is the
projection of a chain `α₂` of `U ∪ V` supported in the trace `pdTr (U ∪ V) (U ∩ V)`, the
corresponding chain of `U ∩ V` (the image of `β` under `pdTrInv`) is itself a relative cycle and
represents the local fundamental class of `c` at `K ∩ L` in the pair `(U ∩ V, (U ∩ V)∖(K ∩ L))`.

The two ingredients are

* the *support transfer* of a chain of the trace `pdTr W W'` to the subspace `W'`
  (`pdTrInv_mem_range_inclChains`), applied to the boundary of `β` (which is supported in the
  complement of `K ∩ L` because `α₂` is);
* the *functoriality of the inclusion of pairs* `(U ∩ V, (U ∩ V)∖(K ∩ L)) → (U ∪ V, (U ∪ V)∖(K ∩ L))`
  (`pdRelChainsMapOf_incl_comp`), which identifies the excision images of the two cycles.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-! ## Two elementary support lemmas -/

/-- **A chain map whose image lies in a subspace has its range inside the chains of that
subspace.**  If `f x ∈ S` for every `x`, then `chainMap f` factors through the inclusion of the
chains of `S`, so its image is contained in their range. -/
theorem chainMap_mem_range_inclChains {X Y : TopCat} (f : X ⟶ Y) (S : Set Y)
    (hf : ∀ x, f x ∈ S) (n : ℕ) (x : (singularChains ℤ X).X n) :
    (chainMap ℤ X Y f).f n x ∈ LinearMap.range ((inclChains Y S).f n).hom := by
  let f' : X ⟶ TopCat.of S := TopCat.ofHom ⟨fun x => ⟨f x, hf x⟩,
    Continuous.subtype_mk ((CategoryTheory.ConcreteCategory.hom f).continuous_toFun) hf⟩
  refine ⟨(chainMap ℤ X (TopCat.of S) f').f n x, ?_⟩
  have hcomp : chainMap ℤ X (TopCat.of S) f' ≫ inclChains Y S = chainMap ℤ X Y f := by
    rw [inclChains, chainMap_compPD]
    congr 1
  have h2 := congrArg (fun (m : singularChains ℤ X ⟶ singularChains ℤ Y) => (m.f n).hom x) hcomp
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2

/-- **Support transfer from the trace of `W'` in `W` to `W'`.**  Let `W' ⊆ W ⊆ M` and `T ⊆ M`.  If
a chain `x` of the trace `pdTr W W'` has image in `C_*(W)` supported in `pdTr W T`, then its image
under the canonical identification `pdTr W W' ≅ W'` (`pdTrInv`) is supported in `pdTr W' T`. -/
theorem pdTrInv_mem_range_inclChains {M : TopCat} {W' W : Set M} (h : W' ⊆ W) (T : Set M)
    {n : ℕ} {x : (singularChains ℤ (TopCat.of (pdTr W W'))).X n}
    (hx : (inclChains (TopCat.of W) (pdTr W W')).f n x
        ∈ LinearMap.range ((inclChains (TopCat.of W) (pdTr W T)).f n).hom) :
    (chainMap ℤ (TopCat.of (pdTr W W')) (TopCat.of W') (pdTrInv h)).f n x
      ∈ LinearMap.range ((inclChains (TopCat.of W') (pdTr W' T)).f n).hom := by
  obtain ⟨z, hz⟩ := hx
  obtain ⟨w, hw⟩ := mem_range_inclChains_of_image_aux (X := TopCat.of W)
      (A := pdTr W T) (V := pdTr W W') n hz.symm
  let D : Set ↥(pdTr W W') := relSubset (X := TopCat.of W) (pdTr W T) (pdTr W W')
  have himg : ∀ y : ↥D,
      (subtypeIncl (TopCat.of (pdTr W W')) D ≫ pdTrInv h) y ∈ pdTr W' T := by
    intro y
    exact y.2
  obtain ⟨z0, hz0⟩ := chainMap_mem_range_inclChains
    (subtypeIncl (TopCat.of (pdTr W W')) D ≫ pdTrInv h) (pdTr W' T) himg n w
  refine ⟨z0, ?_⟩
  rw [hz0, ← hw]
  have hmap : chainMap ℤ (TopCat.of D) (TopCat.of W')
        (subtypeIncl (TopCat.of (pdTr W W')) D ≫ pdTrInv h)
      = inclChains (TopCat.of (pdTr W W')) D
        ≫ chainMap ℤ (TopCat.of (pdTr W W')) (TopCat.of W') (pdTrInv h) := by
    rw [inclChains, chainMap_compPD]
  have h2 := congrArg (fun (m : singularChains ℤ (TopCat.of D)
      ⟶ singularChains ℤ (TopCat.of W')) => (m.f n).hom w) hmap
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2

/-! ## The main statement -/

theorem pd_alpha2_localFundClass {M : TopCat} [T2Space M] {N : ℕ}
    (c : (singularChains ℤ M).homology N) {U V : Set M} (hU : IsOpen U) (hV : IsOpen V)
    (hI : IsOpen (U ∩ V)) {K L : Set M} (hKc : IsCompact K) (hLc : IsCompact L)
    (hKU : K ⊆ U) (hLV : L ⊆ V)
    (α₂ : (singularChains ℤ (TopCat.of ↥(U ∪ V))).X N)
    (β : (singularChains ℤ (TopCat.of ↥(pdTr (U ∪ V) (U ∩ V)))).X N)
    (hβ : (inclChains (TopCat.of ↥(U ∪ V)) (pdTr (U ∪ V) (U ∩ V))).f N β = α₂)
    (hrel : ∃ g, (inclChains (TopCat.of ↥(U ∪ V))
        (pdRelSub (U ∪ V) (K ∩ L))).f (N - 1) g
        = (singularChains ℤ (TopCat.of ↥(U ∪ V))).d N (N - 1) α₂)
    (ζ : (relChains (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∩ L))).cycles N)
    (hζ : (relChains (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∩ L))).iCycles N ζ
        = ((CategoryTheory.Limits.cokernel.π (inclChains (TopCat.of ↥(U ∪ V))
            (pdRelSub (U ∪ V) (K ∩ L)))).f N) α₂)
    (hζc : HomologicalComplex.homologyMap
        (relChainsMap M (U ∪ V) (K ∩ L)ᶜ) N
        ((relChains (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∩ L))).homologyπ N ζ)
      = relLocClass M N c (K ∩ L)) :
    ∃ (γ₂ : (relChains (TopCat.of ↥(U ∩ V)) (pdRelSub (U ∩ V) (K ∩ L))).cycles N),
      (relChains (TopCat.of ↥(U ∩ V)) (pdRelSub (U ∩ V) (K ∩ L))).iCycles N γ₂
        = ((CategoryTheory.Limits.cokernel.π (inclChains (TopCat.of ↥(U ∩ V))
            (pdRelSub (U ∩ V) (K ∩ L)))).f N)
            ((chainMap ℤ (TopCat.of ↥(pdTr (U ∪ V) (U ∩ V))) (TopCat.of ↥(U ∩ V))
              (pdTrInv (Set.inter_subset_left.trans Set.subset_union_left))).f N β) ∧
      (relChains (TopCat.of ↥(U ∩ V)) (pdRelSub (U ∩ V) (K ∩ L))).homologyπ N γ₂
        = localFundClass N c (U ∩ V) hI (K ∩ L)
            (Set.inter_subset_inter hKU hLV) (hKc.inter hLc) := by
  classical
  let W : Set M := U ∪ V
  let W' : Set M := U ∩ V
  have h : W' ⊆ W := Set.inter_subset_left.trans Set.subset_union_left
  let B : Set ↥W := pdRelSub W (K ∩ L)
  let B' : Set ↥W' := pdRelSub W' (K ∩ L)
  let Tt : Set ↥W := pdTr W W'
  let η : (singularChains ℤ (TopCat.of W')).X N :=
    (chainMap ℤ (TopCat.of Tt) (TopCat.of W') (pdTrInv h)).f N β
  have hβ' : (inclChains (TopCat.of W) Tt).f N β = α₂ := hβ
  have hJη : (inclChainsSub M W' W h).f N η = α₂ := by
    have h1 : (inclChains (TopCat.of W) Tt).f N β = (inclChainsSub M W' W h).f N η := by
      have hc := congrArg (fun (m : singularChains ℤ (TopCat.of Tt) ⟶ singularChains ℤ (TopCat.of W)) =>
        (m.f N).hom β) (inclChains_eq_pdTrInv (M := M) h)
      simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hc
      exact hc
    rw [← h1]; exact hβ'
  -- the boundary of β is supported in the complement of K ∩ L inside W
  obtain ⟨g, hg⟩ := hrel
  have hg' : (inclChains (TopCat.of W) B).f (N - 1) g = (singularChains ℤ (TopCat.of W)).d N (N - 1) α₂ := hg
  have hdβ_img : (inclChains (TopCat.of W) Tt).f (N - 1)
        ((singularChains ℤ (TopCat.of Tt)).d N (N - 1) β)
      = (inclChains (TopCat.of W) B).f (N - 1) g := by
    have hcomm : (inclChains (TopCat.of W) Tt).f (N - 1)
          ((singularChains ℤ (TopCat.of Tt)).d N (N - 1) β)
        = (singularChains ℤ (TopCat.of W)).d N (N - 1) ((inclChains (TopCat.of W) Tt).f N β) := by
      have hc := congrArg (fun (m : (singularChains ℤ (TopCat.of Tt)).X N
          ⟶ (singularChains ℤ (TopCat.of W)).X (N - 1)) => (ModuleCat.Hom.hom m) β)
        ((inclChains (TopCat.of W) Tt).comm N (N - 1))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
      exact hc.symm
    rw [hcomm, hβ', ← hg']
  -- descend to W'
  have hdη : (singularChains ℤ (TopCat.of W')).d N (N - 1) η
      ∈ LinearMap.range ((inclChains (TopCat.of W') B').f (N - 1)).hom := by
    have hdd : (singularChains ℤ (TopCat.of W')).d N (N - 1) η
        = (chainMap ℤ (TopCat.of Tt) (TopCat.of W') (pdTrInv h)).f (N - 1)
            ((singularChains ℤ (TopCat.of Tt)).d N (N - 1) β) := by
      have hc := congrArg (fun (m : (singularChains ℤ (TopCat.of Tt)).X N
          ⟶ (singularChains ℤ (TopCat.of W')).X (N - 1)) => (ModuleCat.Hom.hom m) β)
        ((chainMap ℤ (TopCat.of Tt) (TopCat.of W') (pdTrInv h)).comm N (N - 1))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
      exact hc
    have key := pdTrInv_mem_range_inclChains (M := M) (W' := W') (W := W) h ((K ∩ L)ᶜ)
      (n := N - 1) (x := (singularChains ℤ (TopCat.of Tt)).d N (N - 1) β)
      (by
        refine ⟨g, ?_⟩
        exact hdβ_img.symm)
    rw [hdd]
    exact key
  -- the relative cycle
  have hcycle : (relChains (TopCat.of W') B').d N (N - 1)
      (((cokernel.π (inclChains (TopCat.of W') B')).f N) η) = 0 := by
    show ((cokernel (inclChains (TopCat.of W') B')).d N (N - 1))
      (((cokernel.π (inclChains (TopCat.of W') B')).f N) η) = 0
    have hc := congrArg (fun (m : (singularChains ℤ (TopCat.of W')).X N
        ⟶ (cokernel (inclChains (TopCat.of W') B')).X (N - 1)) => (ModuleCat.Hom.hom m) η)
      ((cokernel.π (inclChains (TopCat.of W') B')).comm N (N - 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
    rw [hc]
    obtain ⟨y, hy⟩ := hdη
    rw [← hy]
    exact cokernel_π_f_apply_eq_zero (N - 1) y
  let γ₂ : (relChains (TopCat.of W') B').cycles N :=
    cycleOf N (((cokernel.π (inclChains (TopCat.of W') B')).f N) η) hcycle
  have hγ₂i : (relChains (TopCat.of W') B').iCycles N γ₂
      = ((cokernel.π (inclChains (TopCat.of W') B')).f N) η := iCycles_cycleOf N _ hcycle
  -- the pair map (W', W'∖(K∩L)) → (W, W∖(K∩L))
  let gB : TopCat.of B' ⟶ TopCat.of B := relMapSub B' B (pdIncl W W' h) (fun y hy => hy)
  have hw : subtypeIncl (TopCat.of W') B' ≫ pdIncl W W' h
      = gB ≫ subtypeIncl (TopCat.of W) B :=
    relMapSub_spec B' B (pdIncl W W' h) (fun y hy => hy)
  let Ψ : relChains (TopCat.of W') B' ⟶ relChains (TopCat.of W) B :=
    relChainsMapOf (TopCat.of W') (TopCat.of W) B' B (pdIncl W W' h) gB hw
  have hΨ : (Ψ.f N) (((cokernel.π (inclChains (TopCat.of W') B')).f N) η)
      = ((cokernel.π (inclChains (TopCat.of W) B)).f N) α₂ := by
    have h1 := Crux.cruxRelChainsMapOf_apply B' B (pdIncl W W' h) gB hw N η
    have h2 : (chainMap ℤ (TopCat.of W') (TopCat.of W) (pdIncl W W' h)).f N η = α₂ := by
      rw [pdIncl_eq_inclChainsSub]; exact hJη
    rw [h2] at h1
    simpa only [Ψ] using h1
  -- the two relative cycles have the same underlying chain
  have hcyc : HomologicalComplex.cyclesMap Ψ N γ₂ = ζ := by
    have hinj : Function.Injective (⇑(CategoryTheory.ConcreteCategory.hom
        (HomologicalComplex.iCycles (relChains (TopCat.of W) B) N))) :=
      (ModuleCat.mono_iff_injective
        (HomologicalComplex.iCycles (relChains (TopCat.of W) B) N)).mp inferInstance
    apply hinj
    have h1 := Crux.cruxCyclesMap_i_apply Ψ N γ₂
    rw [hγ₂i] at h1
    rw [h1]
    exact hΨ.trans hζ.symm
  -- the excision image of γ₂ is the local class of c at K ∩ L
  have hKW' : K ∩ L ⊆ W' := Set.inter_subset_inter hKU hLV
  have hKc' : IsCompact (K ∩ L) := hKc.inter hLc
  have hcovW' : W' ∪ (K ∩ L)ᶜ = Set.univ := by
    rw [Set.eq_univ_iff_forall]; intro x
    by_cases hx : x ∈ K ∩ L
    · exact Or.inl (hKW' hx)
    · exact Or.inr hx
  have key : HomologicalComplex.homologyMap (relChainsMap M W' (K ∩ L)ᶜ) N
      ((relChains (TopCat.of W') B').homologyπ N γ₂) = relLocClass M N c (K ∩ L) := by
    let A' : relChains (TopCat.of W') B' ⟶ relChains M (K ∩ L)ᶜ := relChainsMap M W' (K ∩ L)ᶜ
    let A : relChains (TopCat.of W) B ⟶ relChains M (K ∩ L)ᶜ := relChainsMap M W (K ∩ L)ᶜ
    have hfun : Ψ ≫ A = A' := by
      have hcomp := pdRelChainsMapOf_incl_comp (M := M) (W := W) (V := W') h (K ∩ L)
        (fun y hy => hy)
      simpa only [Ψ, A, A', gB, hw] using hcomp
    have hnat1 : HomologicalComplex.homologyMap Ψ N
        ((relChains (TopCat.of W') B').homologyπ N γ₂)
        = (relChains (TopCat.of W) B).homologyπ N (HomologicalComplex.cyclesMap Ψ N γ₂) := by
      have hc := congrArg (fun (m : (relChains (TopCat.of W') B').cycles N
          ⟶ (relChains (TopCat.of W) B).homology N) => (ModuleCat.Hom.hom m) γ₂)
        (HomologicalComplex.homologyπ_naturality Ψ N)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
      exact hc
    calc HomologicalComplex.homologyMap A' N ((relChains (TopCat.of W') B').homologyπ N γ₂)
        = HomologicalComplex.homologyMap (Ψ ≫ A) N
            ((relChains (TopCat.of W') B').homologyπ N γ₂) := by rw [hfun]
      _ = HomologicalComplex.homologyMap A N
            (HomologicalComplex.homologyMap Ψ N
              ((relChains (TopCat.of W') B').homologyπ N γ₂)) := by
            rw [HomologicalComplex.homologyMap_comp]; rfl
      _ = HomologicalComplex.homologyMap A N
            ((relChains (TopCat.of W) B).homologyπ N
              (HomologicalComplex.cyclesMap Ψ N γ₂)) := by rw [hnat1]
      _ = HomologicalComplex.homologyMap A N
            ((relChains (TopCat.of W) B).homologyπ N ζ) := by rw [hcyc]
      _ = relLocClass M N c (K ∩ L) := hζc
  -- conclude
  refine ⟨γ₂, hγ₂i, ?_⟩
  haveI : IsIso (HomologicalComplex.homologyMap (relChainsMap M W' (K ∩ L)ᶜ) N) :=
    excision_relChainsMap_isIso M W' (K ∩ L)ᶜ hI hKc'.isClosed.isOpen_compl hcovW' N
  have hspec := localFundClass_spec N c W' hI (K ∩ L) hKW' hKc'
  calc (relChains (TopCat.of W') B').homologyπ N γ₂
      = CategoryTheory.inv (HomologicalComplex.homologyMap (relChainsMap M W' (K ∩ L)ᶜ) N)
          (HomologicalComplex.homologyMap (relChainsMap M W' (K ∩ L)ᶜ) N
            ((relChains (TopCat.of W') B').homologyπ N γ₂)) :=
          (CategoryTheory.IsIso.hom_inv_id_apply _ _).symm
    _ = CategoryTheory.inv (HomologicalComplex.homologyMap (relChainsMap M W' (K ∩ L)ᶜ) N)
          (relLocClass M N c (K ∩ L)) := by rw [key]
    _ = CategoryTheory.inv (HomologicalComplex.homologyMap (relChainsMap M W' (K ∩ L)ᶜ) N)
          (HomologicalComplex.homologyMap (relChainsMap M W' (K ∩ L)ᶜ) N
            (localFundClass N c W' hI (K ∩ L) hKW' hKc')) := by rw [hspec]
    _ = localFundClass N c W' hI (K ∩ L) hKW' hKc' := CategoryTheory.IsIso.hom_inv_id_apply _ _

end

end Work.Cohomology

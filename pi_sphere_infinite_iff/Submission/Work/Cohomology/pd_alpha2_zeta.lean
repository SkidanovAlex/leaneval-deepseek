import Mathlib
import Submission.Work.Cohomology.pd_glue3
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.pd_plumbing
import Submission.Work.Cohomology.pd_localFundClass_natural

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-! ## Two generalities on `cyclesMap`

These are stated for an arbitrary morphism of chain complexes of `ℤ`-modules so that they can be
applied to the morphisms of relative chain complexes without running into the definitional
unfolding of the `abbrev relChains`. -/

/-- **Naturality of `homologyπ`**: a morphism of complexes sends the homology class of a cycle to
the homology class of the image cycle. -/
lemma homologyMap_homologyπ_cyclesMap {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) (N : ℕ)
    (z : K.cycles N) :
    (HomologicalComplex.homologyMap φ N).hom ((K.homologyπ N).hom z)
      = (L.homologyπ N).hom ((HomologicalComplex.cyclesMap φ N).hom z) := by
  have h2 := congrArg (fun (g : K.cycles N ⟶ L.homology N) => g.hom z)
    (HomologicalComplex.homologyπ_naturality φ N)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- The underlying chain of the image cycle is the image of the underlying chain. -/
lemma iCycles_cyclesMap_apply {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) (N : ℕ)
    (z : K.cycles N) :
    (L.iCycles N).hom ((HomologicalComplex.cyclesMap φ N).hom z)
      = (φ.f N).hom ((K.iCycles N).hom z) := by
  have h2 := congrArg (fun (g : K.cycles N ⟶ L.X N) => g.hom z)
    (HomologicalComplex.cyclesMap_i φ N)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- **A chain supported in a subset of the contracted part is killed by the projection to the
relative chain complex.**  If `A ⊆ A₀ ⊆ X`, then the composite `C_*(A) → C_*(X) → C_*(X,A₀)` is
zero (it factors through the inclusion `C_*(A₀) → C_*(X)`, whose cokernel is `C_*(X,A₀)`). -/
theorem coker_π_inclChains_apply_eq_zero_of_subset {X : TopCat} {A A₀ : Set X} (h : A ⊆ A₀)
    (n : ℕ) (y : (singularChains ℤ (TopCat.of ↥A)).X n) :
    ((cokernel.π (inclChains X A₀)).f n) ((inclChains X A).f n y) = 0 := by
  have h1 : ((inclChainsSub X A A₀ h).f n ≫ (inclChains X A₀).f n) = (inclChains X A).f n := by
    have hc := congrArg (fun (φ : singularChains ℤ (TopCat.of ↥A) ⟶ singularChains ℤ X) => φ.f n)
      (inclChainsSub_comp X A A₀ h)
    rwa [HomologicalComplex.comp_f] at hc
  rw [← h1, ModuleCat.comp_apply]
  exact cokernel_π_f_apply_eq_zero n _

/-- **The middle summand of the Hatcher splitting represents the local fundamental class at
`K ∩ L`.**

Let `W ⊆ M` be open, `K, L ⊆ W` compact, and let `ξ ∈ C_N(W)` be a chain whose image in
`C_N(W, W∖(K∪L))` is a relative cycle `γ` representing the local fundamental class of `c` at
`K ∪ L`.  Suppose `ξ = α₁ + α₂ + α₃`, where `α₁` is supported in a subset `S₁ ⊆ W∖(K∩L)` of `W`
and `α₃` in a subset `S₃ ⊆ W∖(K∩L)`.

Then the middle summand `α₂` already represents the local fundamental class at `K ∩ L`: its image
`π α₂` in `C_N(W, W∖(K∩L))` is a relative cycle, and the class of that cycle is carried by the
excision map `H_N(W, W∖(K∩L)) → H_N(M, M∖(K∩L))` to `relLocClass M N c (K ∩ L)`.

The proof is formal: the images of `α₁` and `α₃` under the projection to `C_*(W, W∖(K∩L))` vanish
(they are supported in the contracted part), so that projection of `ξ` equals the projection of
`α₂`; and that projection of `ξ` is the image of the cycle `γ` under the chain map
`C_*(W, W∖(K∪L)) → C_*(W, W∖(K∩L))`, hence a cycle whose class is the image of the class of `γ`,
which by `pd_localFundClass_natural` is the local fundamental class at `K ∩ L`. -/
theorem pd_alpha2_zeta_gen {M : TopCat} [T2Space M] {N : ℕ}
    (c : (singularChains ℤ M).homology N) {W : Set M} (hW : IsOpen W)
    {K L : Set M} (hKc : IsCompact K) (hLc : IsCompact L) (hKW : K ⊆ W) (hLW : L ⊆ W)
    (ξ : (singularChains ℤ (TopCat.of ↥W)).X N)
    (γ : (relChains (TopCat.of ↥W) (pdRelSub W (K ∪ L))).cycles N)
    (hγ : (relChains (TopCat.of ↥W) (pdRelSub W (K ∪ L))).iCycles N γ
        = ((cokernel.π (inclChains (TopCat.of ↥W) (pdRelSub W (K ∪ L)))).f N) ξ)
    (hγc : (relChains (TopCat.of ↥W) (pdRelSub W (K ∪ L))).homologyπ N γ
        = localFundClass N c W hW (K ∪ L) (Set.union_subset hKW hLW) (hKc.union hLc))
    (α₁ α₂ α₃ : (singularChains ℤ (TopCat.of ↥W)).X N)
    (hξ : ξ = α₁ + α₂ + α₃)
    {S₁ S₃ : Set ↥W} (hS₁ : S₁ ⊆ pdRelSub W (K ∩ L)) (hS₃ : S₃ ⊆ pdRelSub W (K ∩ L))
    (hα₁ : ∃ a', (inclChains (TopCat.of ↥W) S₁).f N a' = α₁)
    (hα₃ : ∃ d', (inclChains (TopCat.of ↥W) S₃).f N d' = α₃) :
    ∃ (ζ : (relChains (TopCat.of ↥W) (pdRelSub W (K ∩ L))).cycles N),
      (relChains (TopCat.of ↥W) (pdRelSub W (K ∩ L))).iCycles N ζ
        = ((cokernel.π (inclChains (TopCat.of ↥W) (pdRelSub W (K ∩ L)))).f N) α₂ ∧
      HomologicalComplex.homologyMap (relChainsMap M W (K ∩ L)ᶜ) N
        ((relChains (TopCat.of ↥W) (pdRelSub W (K ∩ L))).homologyπ N ζ)
        = relLocClass M N c (K ∩ L) := by
  classical
  have hKL : K ∩ L ⊆ K ∪ L := Set.inter_subset_left.trans Set.subset_union_left
  have hAK : pdRelSub W (K ∪ L) ⊆ pdRelSub W (K ∩ L) := pdRelSub_mono hKL
  have hKLW : K ∩ L ⊆ W := fun x hx => hKW hx.1
  -- the two outer summands are killed by the projection to the pair `(W, W∖(K ∩ L))`
  have hkill₁ : ((cokernel.π (inclChains (TopCat.of ↥W) (pdRelSub W (K ∩ L)))).f N) α₁ = 0 := by
    obtain ⟨a', ha'⟩ := hα₁
    rw [← ha']
    exact coker_π_inclChains_apply_eq_zero_of_subset hS₁ N a'
  have hkill₃ : ((cokernel.π (inclChains (TopCat.of ↥W) (pdRelSub W (K ∩ L)))).f N) α₃ = 0 := by
    obtain ⟨d', hd'⟩ := hα₃
    rw [← hd']
    exact coker_π_inclChains_apply_eq_zero_of_subset hS₃ N d'
  have hξA : ((cokernel.π (inclChains (TopCat.of ↥W) (pdRelSub W (K ∩ L)))).f N) ξ
      = ((cokernel.π (inclChains (TopCat.of ↥W) (pdRelSub W (K ∩ L)))).f N) α₂ := by
    rw [hξ, map_add, map_add, hkill₁, hkill₃]
    simp
  -- the same statements, in the `ModuleCat.Hom.hom` form used by the `cyclesMap` lemmas
  have hγ' : (HomologicalComplex.iCycles (cokernel (inclChains (TopCat.of ↥W)
        (pdRelSub W (K ∪ L)))) N).hom γ
      = ((cokernel.π (inclChains (TopCat.of ↥W) (pdRelSub W (K ∪ L)))).f N).hom ξ := hγ
  have hγc' : (HomologicalComplex.homologyπ (cokernel (inclChains (TopCat.of ↥W)
        (pdRelSub W (K ∪ L)))) N).hom γ
      = localFundClass N c W hW (K ∪ L) (Set.union_subset hKW hLW) (hKc.union hLc) := hγc
  have hξA' : ((cokernel.π (inclChains (TopCat.of ↥W) (pdRelSub W (K ∩ L)))).f N).hom ξ
      = ((cokernel.π (inclChains (TopCat.of ↥W) (pdRelSub W (K ∩ L)))).f N).hom α₂ := hξA
  -- the compatibility of the projection with the map of relative chain complexes
  have hcomp : ((relCokerMap (TopCat.of ↥W) (pdRelSub W (K ∪ L)) (pdRelSub W (K ∩ L)) hAK).f N).hom
        (((cokernel.π (inclChains (TopCat.of ↥W) (pdRelSub W (K ∪ L)))).f N).hom ξ)
      = ((cokernel.π (inclChains (TopCat.of ↥W) (pdRelSub W (K ∩ L)))).f N).hom ξ := by
    have h := congrArg (fun (g : singularChains ℤ (TopCat.of ↥W) ⟶
        relChains (TopCat.of ↥W) (pdRelSub W (K ∩ L))) => (g.f N).hom ξ)
      (relCokerMap_comp_π (TopCat.of ↥W) (pdRelSub W (K ∪ L)) (pdRelSub W (K ∩ L)) hAK)
    simp only [HomologicalComplex.comp_f] at h
    exact h
  refine ⟨HomologicalComplex.cyclesMap (relCokerMap (TopCat.of ↥W) (pdRelSub W (K ∪ L))
    (pdRelSub W (K ∩ L)) hAK) N γ, ?_, ?_⟩
  · -- the underlying chain of the middle piece is the projection of `α₂`
    have hci := iCycles_cyclesMap_apply (relCokerMap (TopCat.of ↥W) (pdRelSub W (K ∪ L))
      (pdRelSub W (K ∩ L)) hAK) N γ
    rw [hγ', hcomp, hξA'] at hci
    exact hci
  · -- the class of the middle piece is the local fundamental class at `K ∩ L`
    have hnat := homologyMap_homologyπ_cyclesMap (relCokerMap (TopCat.of ↥W) (pdRelSub W (K ∪ L))
      (pdRelSub W (K ∩ L)) hAK) N γ
    have hnat2 : (HomologicalComplex.homologyMap (relCokerMap (TopCat.of ↥W) (pdRelSub W (K ∪ L))
          (pdRelSub W (K ∩ L)) hAK) N).hom
          (localFundClass N c W hW (K ∪ L) (Set.union_subset hKW hLW) (hKc.union hLc))
        = localFundClass N c W hW (K ∩ L) hKLW (hKc.inter hLc) :=
      pd_localFundClass_natural N c W hW hKL hKLW (Set.union_subset hKW hLW) (hKc.inter hLc)
        (hKc.union hLc)
    rw [hγc'] at hnat
    have hclass : (relChains (TopCat.of ↥W) (pdRelSub W (K ∩ L))).homologyπ N
          (HomologicalComplex.cyclesMap (relCokerMap (TopCat.of ↥W) (pdRelSub W (K ∪ L))
            (pdRelSub W (K ∩ L)) hAK) N γ)
        = localFundClass N c W hW (K ∩ L) hKLW (hKc.inter hLc) := hnat.symm.trans hnat2
    rw [hclass]
    exact localFundClass_spec N c W hW (K ∩ L) hKLW (hKc.inter hLc)

theorem pd_alpha2_zeta {M : TopCat} [T2Space M] {N : ℕ}
    (c : (singularChains ℤ M).homology N) {U V : Set M} (hU : IsOpen U) (hV : IsOpen V)
    {K L : Set M} (hKc : IsCompact K) (hLc : IsCompact L) (hKU : K ⊆ U) (hLV : L ⊆ V)
    (ξ : (singularChains ℤ (TopCat.of ↥(U ∪ V))).X N)
    (γ : (relChains (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∪ L))).cycles N)
    (hγ : (relChains (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∪ L))).iCycles N γ
        = ((CategoryTheory.Limits.cokernel.π (inclChains (TopCat.of ↥(U ∪ V))
            (pdRelSub (U ∪ V) (K ∪ L)))).f N) ξ)
    (hγc : (relChains (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∪ L))).homologyπ N γ
        = localFundClass N c (U ∪ V) (hU.union hV) (K ∪ L)
            (Set.union_subset (hKU.trans Set.subset_union_left) (hLV.trans Set.subset_union_right))
            (hKc.union hLc))
    (α₁ α₂ α₃ : (singularChains ℤ (TopCat.of ↥(U ∪ V))).X N)
    (hξ : ξ = α₁ + α₂ + α₃)
    (hα₁ : ∃ a', (inclChains (TopCat.of ↥(U ∪ V))
        (pdTr (U ∪ V) (U \ L))).f N a' = α₁)
    (hα₃ : ∃ d', (inclChains (TopCat.of ↥(U ∪ V))
        (pdTr (U ∪ V) (V \ K))).f N d' = α₃) :
    ∃ (ζ : (relChains (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∩ L))).cycles N),
      (relChains (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∩ L))).iCycles N ζ
        = ((CategoryTheory.Limits.cokernel.π (inclChains (TopCat.of ↥(U ∪ V))
            (pdRelSub (U ∪ V) (K ∩ L)))).f N) α₂ ∧
      HomologicalComplex.homologyMap (relChainsMap M (U ∪ V) (K ∩ L)ᶜ) N
        ((relChains (TopCat.of ↥(U ∪ V)) (pdRelSub (U ∪ V) (K ∩ L))).homologyπ N ζ)
        = relLocClass M N c (K ∩ L) := by
  refine pd_alpha2_zeta_gen (W := U ∪ V) (K := K) (L := L) (S₁ := pdTr (U ∪ V) (U \ L))
    (S₃ := pdTr (U ∪ V) (V \ K)) c (hU.union hV) hKc hLc
    (fun x hx => Set.subset_union_left (hKU hx))
    (fun x hx => Set.subset_union_right (hLV hx)) ξ γ hγ hγc α₁ α₂ α₃ hξ
    (fun y hy hmem => hy.2 hmem.2) (fun y hy hmem => hy.2 hmem.1) hα₁ hα₃

end

end Work.Cohomology

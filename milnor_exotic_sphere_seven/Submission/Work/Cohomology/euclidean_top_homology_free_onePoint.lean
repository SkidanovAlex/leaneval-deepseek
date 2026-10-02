import Mathlib
import Submission.Work.Cohomology.Singular
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.localHomology_top_free_onePoint
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.onePointSpace_compl_point_homeo
import Submission.Work.Cohomology.homology_onePointSpace_free
import Submission.Work.Cohomology.free_and_vanishing_ball_compl
import Submission.Work.Cohomology.free_homology_iUnion_of_split
import Submission.Work.Cohomology.onePoint_relChainsInclSet_functorial
import Submission.Work.Cohomology.onePoint_cokernel_pi_compl_point_bijective
import Submission.Work.Cohomology.sphereHomologyTop

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `(N-1)`-st homology of an open subset of the one-point compactification of `ℝ^N` is free

For `N ≥ 1` and an open set `U ⊆ OnePoint (EuclideanSpace ℝ (Fin N)) = S^N`, the `(N-1)`-st
singular homology `H_{N-1}(U; ℤ)` is a free `ℤ`-module.

The proof is the Alexander-duality argument run through the long exact sequence of the pair
`(S, U)`:

* `H_N(S, U)` is free (`Work.Cohomology.localHomology_top_free_onePoint`, since `S ∖ U` is a
  compact subset of the `N`-manifold `S`);
* the map `i : H_N(S) ⟶ H_N(S, U)` of the pair sequence has `range i = ker ∂`, where
  `∂ : H_N(S, U) ⟶ H_{N-1}(U)` is the connecting map (`Work.Cohomology.hPair_exact₃`), and `∂` is
  surjective because `H_{N-1}(S) = 0` (`Work.Cohomology.onePoint_hPairdelta_surjective`);
* collapsing a point `pt ∉ U` gives a retraction: the map `r : H_N(S, U) ⟶ H_N(S, {pt}ᶜ)` of
  `Work.Cohomology.onePoint_relChainsInclSet_functorial` composes with `i` to the pair map
  `H_N(S) ⟶ H_N(S, {pt}ᶜ)`, which is bijective
  (`Work.Cohomology.onePoint_cokernel_pi_compl_point_bijective`) because `{pt}ᶜ ≅ ℝ^N` has
  vanishing homology in degrees `N` and `N-1`.  Hence `i` is a split monomorphism;
* therefore `H_{N-1}(U) ≅ H_N(S,U) / range i` is the complementary summand `ker l` of a left
  inverse `l` of `i`, hence free as a submodule of the free `ℤ`-module `H_N(S, U)`
  (`Work.Cohomology.free_quot_of_split_mono`).

The degenerate cases are `N = 1` (`H_0` of any space is free, `Work.Cohomology.homology_zero_free`)
and `U = S` (`H_{N-1}(S)` is free, `Work.Cohomology.homology_onePointSpace_free`).
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace Work.Cohomology

noncomputable section

attribute [local instance 5000] Submodule.module

/-- **Freeness of a quotient by a split-injective submodule.**

Let `i : M0 ⟶ M1` admit a left inverse `l` and let `d : M1 ⟶ M2` be surjective with
`ker d = range i`.  Then `M2 ≅ ker l` is a submodule of the free module `M1`, hence free. -/
theorem free_quot_of_split_mono {M0 M1 M2 : Type*} [AddCommGroup M0] [Module ℤ M0]
    [AddCommGroup M1] [Module ℤ M1] [AddCommGroup M2] [Module ℤ M2] [Module.Free ℤ M1]
    (i : M0 →ₗ[ℤ] M1) (d : M1 →ₗ[ℤ] M2) (hker : d.ker = i.range)
    (hsurj : Function.Surjective d) (l : M1 →ₗ[ℤ] M0) (hl : l.comp i = LinearMap.id) :
    Module.Free ℤ M2 := by
  have hli : ∀ x : M0, l (i x) = x := by
    intro x
    have h := congrArg (fun f : M0 →ₗ[ℤ] M0 => f x) hl
    simpa [LinearMap.comp_apply] using h
  -- `range i` and `ker l` are complementary submodules of `M1`
  have hdisj : Disjoint (LinearMap.range i) (LinearMap.ker l) := by
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    obtain ⟨a, rfl⟩ := hx1
    have h0 : a = 0 := by rw [← hli a]; exact hx2
    rw [h0, map_zero]
  have hsup : LinearMap.range i ⊔ LinearMap.ker l = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    rw [Submodule.mem_sup]
    refine ⟨i (l x), LinearMap.mem_range_self i (l x), x - i (l x), ?_, ?_⟩
    · rw [LinearMap.mem_ker, map_sub, hli (l x), sub_self]
    · abel
  -- the restriction of `d` to the complement `ker l` is bijective
  have hφker : LinearMap.ker (d.comp (LinearMap.ker l).subtype) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx1 : (x : M1) ∈ LinearMap.ker d := by
      have : (d.comp (LinearMap.ker l).subtype) x = 0 := hx
      simpa using this
    have hx2 : (x : M1) ∈ LinearMap.range i := by rw [← hker]; exact hx1
    have hboth : (x : M1) ∈ LinearMap.range i ⊓ LinearMap.ker l := ⟨hx2, x.2⟩
    rw [disjoint_iff.mp hdisj, Submodule.mem_bot] at hboth
    exact Subtype.ext hboth
  have hφsurj : Function.Surjective (d.comp (LinearMap.ker l).subtype) := by
    intro y
    obtain ⟨m, hm⟩ := hsurj y
    have hmem : i (l m) ∈ LinearMap.ker d := by
      rw [hker]; exact LinearMap.mem_range_self i (l m)
    have h0 : d (i (l m)) = 0 := hmem
    refine ⟨⟨m - i (l m), ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker, map_sub, hli (l m), sub_self]
    · show d (m - i (l m)) = y
      rw [map_sub, h0, sub_zero, hm]
  have hbij : Function.Bijective (d.comp (LinearMap.ker l).subtype) :=
    ⟨LinearMap.ker_eq_bot.mp hφker, hφsurj⟩
  let e : ↥(LinearMap.ker l) ≃ₗ[ℤ] M2 :=
    LinearEquiv.ofBijective (d.comp (LinearMap.ker l).subtype) hbij
  exact Module.Free.of_equiv' (free_submodule_of_free (LinearMap.ker l)) e

theorem euclidean_top_homology_free_onePoint {N : ℕ} (hN : 1 ≤ N)
    (U : Set (OnePoint (EuclideanSpace ℝ (Fin N)))) (hU : IsOpen U) :
    Module.Free ℤ ↥((Work.Cohomology.singularChains ℤ (TopCat.of ↥U)).homology (N - 1)) := by
  rcases eq_or_lt_of_le hN with h1 | h2
  · -- `N = 1`: the degree is `0` and `H_0` of any space is free
    subst h1
    simpa using homology_zero_free (TopCat.of ↥U)
  · obtain ⟨k, rfl⟩ : ∃ k, N = k + 2 := ⟨N - 2, by omega⟩
    rcases Set.eq_empty_or_nonempty (Uᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin (k+2))))) with hUc | hne
    · -- `U = S`: `H_{N-1}(S)` is free
      have hUuniv : U = Set.univ := by
        rw [← compl_compl U, hUc, Set.compl_empty]
      exact moduleFree_homology_of_homeomorph
        ((Homeomorph.setCongr hUuniv).trans (Homeomorph.Set.univ _))
        (k + 2 - 1) (homology_onePointSpace_free (k + 2) (by omega))
    · -- the complement of `U` is a nonempty compact set
      obtain ⟨pt, hpt⟩ := hne
      have hptU : pt ∉ U := hpt
      have hK : IsCompact (Uᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin (k+2))))) :=
        hU.isClosed_compl.isCompact
      have hfreeM1 : Module.Free ℤ ↥((Work.Cohomology.relChains
          (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin (k+2))))) U).homology (k+2)) := by
        have h := localHomology_top_free_onePoint (N := k+2) (by omega) (Uᶜ) hK
        rwa [compl_compl] at h
      -- the maps of the pair sequence
      let i : ↥((Work.Cohomology.singularChains ℤ
            (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin (k+2)))))).homology (k+2))
          →ₗ[ℤ] ↥((Work.Cohomology.relChains
            (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin (k+2))))) U).homology (k+2)) :=
        (HomologicalComplex.homologyMap (cokernel.π (inclChains
          (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin (k+2))))) U)) (k+2)).hom
      let d : ↥((Work.Cohomology.relChains
            (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin (k+2))))) U).homology (k+2))
          →ₗ[ℤ] ↥((Work.Cohomology.singularChains ℤ (TopCat.of ↥U)).homology (k+2-1)) :=
        (hPairδ (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin (k+2))))) U (k+1)).hom
      let r : ↥((Work.Cohomology.relChains
            (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin (k+2))))) U).homology (k+2))
          →ₗ[ℤ] ↥((Work.Cohomology.relChains (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin (k+2)))))
            ({pt}ᶜ)).homology (k+2)) :=
        (HomologicalComplex.homologyMap (relChainsInclSet
          (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin (k+2)))))
          (Set.subset_compl_singleton_iff.mpr hptU)) (k+2)).hom
      let i' : ↥((Work.Cohomology.singularChains ℤ
            (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin (k+2)))))).homology (k+2))
          →ₗ[ℤ] ↥((Work.Cohomology.relChains (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin (k+2)))))
            ({pt}ᶜ)).homology (k+2)) :=
        (HomologicalComplex.homologyMap (cokernel.π (inclChains
          (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin (k+2))))) ({pt}ᶜ))) (k+2)).hom
      -- exactness of the pair sequence at `H_N(S,U)`
      have hker : d.ker = i.range := by
        have hex := ShortComplex.Exact.moduleCat_range_eq_ker
          (hPair_exact₃ (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin (k+2))))) U (k+1))
        exact hex.symm
      -- `H_{N-1}(S) = 0`, so the connecting map of the pair sequence is surjective
      have hzero : IsZero ((Work.Cohomology.singularChains ℤ
          (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin (k+2)))))).homology (k+1)) := by
        let e : OnePointSpace (k+2) ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (k+2+1))) 1 :=
          onePointEquivSphereOfFinrankEq (V := EuclideanSpace ℝ (Fin (k+2)))
            (ι := Fin (k+2+1)) (by simp)
        obtain ⟨iso⟩ := homologyIso_of_homotopyEquiv e.toHomotopyEquiv (k+1)
        exact IsZero.of_iso (sphereVanishing (k+2) (k+1) (by omega) (by omega) (by omega)) iso
      have hsurj : Function.Surjective d := by
        have hex := ShortComplex.Exact.moduleCat_range_eq_ker
          (hPair_exact₁ (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin (k+2))))) U (k+1))
        have h0 : HomologicalComplex.homologyMap (inclChains
            (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin (k+2))))) U) (k+1) = 0 :=
          IsZero.eq_zero_of_tgt hzero _
        have hz : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (inclChains
            (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin (k+2))))) U) (k+1))).ker = ⊤ := by
          rw [h0, ModuleCat.hom_zero, LinearMap.ker_zero]
        have : (ModuleCat.Hom.hom
            (hPairδ (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin (k+2))))) U (k+1))).range = ⊤ := by
          rw [hex, hz]
        exact LinearMap.range_eq_top.mp this
      have hbij : Function.Bijective i' :=
        onePoint_cokernel_pi_compl_point_bijective (N := k+2) (by omega) pt
      -- functoriality: `r ∘ i = i'`
      have hfun : r.comp i = i' := by
        have h := onePoint_relChainsInclSet_functorial (N := k+2) U pt hptU
        have h2 := congrArg ModuleCat.Hom.hom h
        rw [ModuleCat.hom_comp] at h2
        exact h2
      -- the left inverse of `i`
      let i'L : ↥((Work.Cohomology.singularChains ℤ
            (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin (k+2)))))).homology (k+2))
          ≃ₗ[ℤ] ↥((Work.Cohomology.relChains (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin (k+2)))))
            ({pt}ᶜ)).homology (k+2)) :=
        LinearEquiv.ofBijective i' hbij
      let l : ↥((Work.Cohomology.relChains
            (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin (k+2))))) U).homology (k+2))
          →ₗ[ℤ] ↥((Work.Cohomology.singularChains ℤ
            (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin (k+2)))))).homology (k+2)) :=
        i'L.symm.toLinearMap.comp r
      have hl : l.comp i = LinearMap.id := by
        ext x
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        change i'L.symm (r (i x)) = x
        rw [show r (i x) = i' x from by
          have h := congrArg (fun f => f x) hfun
          simpa [LinearMap.comp_apply] using h]
        exact i'L.symm_apply_apply x
      haveI := hfreeM1
      exact free_quot_of_split_mono i d hker hsurj l hl

end

end Work.Cohomology

import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_goodD_natural
import Submission.Work.Cohomology.pd_goodD_incl
import Submission.Work.Projective.GoodCp2.fork.local_generator_convex
import Submission.Work.Cohomology.chartConvexPair_relHomology_iso
import Submission.Work.Cohomology.Duality.ball_local_homology
import Submission.Work.Cohomology.Duality.euclidean_convex_local_cohomology
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.relCohomologyDual
import Submission.Work.Cohomology.pd_coordinate_ball
import Submission.Work.Projective.GoodCp2.fork.pd_good_coordinate_ball

set_option synthInstance.maxHeartbeats 400000

/-!
# The base case of the `Good` framework: a convex coordinate set

`Work.Cohomology.Good N c W hW` is the elementwise form of "the duality map with compact supports
`H^k_c(W) → H_{N-k}(W)`, `x ↦ x ⌢ μ_W`, is bijective" (see `Work.Cohomology.pd_good`).

This file proves the base case for an arbitrary *convex* open set in a coordinate chart, which is
the form needed to glue coordinate balls: for

`W = e ⁻¹' Q ∩ e.source`,   `e = chartAt _ cc`,   `Q ⊆ Metric.ball (e cc) r ⊆ e.target` open,
convex and nonempty,

one has `Good N c W`.  The proof is the same as for a coordinate ball
(`Work.Cohomology.pd_good_coordinate_ball`):

* `W` is homeomorphic to the convex set `Q`, hence contractible, so `H_m(W) = 0` for `m ≥ 1`;
* for a compact convex `KK ⊆ Q` and `K = e ⁻¹' KK ∩ e.source`, the pair `(W, W∖K)` has the relative
  homology of `(ℝ^N, ℝ^N∖KK)` (`chartConvexPair_relHomology_iso`), which is `ℤ` in degree `N` and
  vanishes elsewhere (`Duality.ball_local_homology`), and is free (`Duality.free_relChains_compl`);
* the local fundamental class of `c` at `K` generates `H_N(W, W∖K)` (`local_generator_convex`);
* the top-degree cap product with a generator is bijective (`relCapPair_top_bijective`, packaged as
  `goodD_top_bijective`).

The two clauses of `Good` are then: *hit* — for `k = N` use the bijectivity at the one-point set
`KK = {e z}` (`z ∈ W` any point), for `k ≠ N` the target `H_{N-k}(W)` vanishes; *kill* — enlarge a
compact `K ⊆ W` to the convex hull of `e '' K ∪ {e z}`, where the top-degree map is bijective and
the source vanishes for `k ≠ N`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

namespace Work.Cohomology

noncomputable section

theorem pd_good_convex (N : ℕ) (hN : 1 ≤ N) (M : TopCat) [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M]
    (c : (Work.Cohomology.singularChains ℤ M).homology N)
    (hc : ∀ x : M, Submodule.span ℤ
      {((HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains M {y | y ≠ x})) N) c)} = ⊤)
    (cc : M) (r : ℝ) (hr : 0 < r) :
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)) := chartAt _ cc
    Metric.ball (e cc) r ⊆ e.target →
    (Q : Set (EuclideanSpace ℝ (Fin N))) → IsOpen Q → Convex ℝ Q → Q.Nonempty →
      Q ⊆ Metric.ball (e cc) r →
    let W : Set M := (e ⁻¹' Q) ∩ e.source
    ∀ (hW : IsOpen W), Work.Cohomology.Good N c W hW := by
  intro e hball Q hQopen hQconv hQne hQball W hW
  obtain ⟨v₀, hv₀⟩ := hQne
  have hQsub : Q ⊆ e.target := fun v hv => hball (hQball hv)
  -- the point `z = e.symm v₀` of `W`
  have hv₀tgt : v₀ ∈ e.target := hQsub hv₀
  have hzsrc : e.symm v₀ ∈ e.source := e.map_target hv₀tgt
  have hez : e (e.symm v₀) = v₀ := e.right_inv hv₀tgt
  have hzQ : e (e.symm v₀) ∈ Q := by rw [hez]; exact hv₀
  have hzW : e.symm v₀ ∈ W := ⟨hzQ, hzsrc⟩
  -- `W` is homeomorphic to `Q`, hence contractible
  have hW' : W = e.source ∩ e ⁻¹' Q := by
    show (e ⁻¹' Q) ∩ e.source = e.source ∩ e ⁻¹' Q
    rw [Set.inter_comm]
  haveI hQcontr : ContractibleSpace ↥Q := Convex.contractibleSpace hQconv ⟨v₀, hv₀⟩
  haveI hcontr : ContractibleSpace ↥(TopCat.of W) :=
    Homeomorph.contractibleSpace
      ((Homeomorph.setCongr hW').trans (partialHomeomorphSetHomeo e hQsub))
  -- a compact convex `KK ⊆ Q` gives a compact `K = e ⁻¹' KK ∩ e.source ⊆ W`
  have key_sub : ∀ (KK : Set (EuclideanSpace ℝ (Fin N))), KK ⊆ Q →
      ((e ⁻¹' KK) ∩ e.source) ⊆ W := by
    intro KK hKKQ y hy
    exact ⟨hKKQ hy.1, hy.2⟩
  have key_compact : ∀ (KK : Set (EuclideanSpace ℝ (Fin N))), IsCompact KK → KK ⊆ Q →
      IsCompact ((e ⁻¹' KK) ∩ e.source) := by
    intro KK hKKc hKKQ
    have hKKtgt : KK ⊆ e.target := hKKQ.trans hQsub
    have heq : (e ⁻¹' KK) ∩ e.source = e.symm '' KK := by
      rw [Set.inter_comm, ← OpenPartialHomeomorph.symm_image_eq_source_inter_preimage e hKKtgt]
    rw [heq]
    exact hKKc.image_of_continuousOn (e.continuousOn_symm.mono hKKtgt)
  -- the model and generator package for a compact convex `KK ⊆ Q`
  have key : ∀ (KK : Set (EuclideanSpace ℝ (Fin N))) (hKKc : IsCompact KK) (hKKconv : Convex ℝ KK)
      (hKKQ : KK ⊆ Q) (hzKK : e (e.symm v₀) ∈ KK)
      (hKW : ((e ⁻¹' KK) ∩ e.source) ⊆ W)
      (hKc : IsCompact ((e ⁻¹' KK) ∩ e.source)),
      (∀ i, Module.Free ℤ
          ↥((relChains (TopCat.of W) (pdRelSub W ((e ⁻¹' KK) ∩ e.source))).homology i)) ∧
      Nonempty ((relChains (TopCat.of W) (pdRelSub W ((e ⁻¹' KK) ∩ e.source))).homology N
        ≅ ModuleCat.of ℤ ℤ) ∧
      (∀ i, i ≠ N → IsZero
          ((relChains (TopCat.of W) (pdRelSub W ((e ⁻¹' KK) ∩ e.source))).homology i)) ∧
      (Submodule.span ℤ
        {localFundClass N c W hW ((e ⁻¹' KK) ∩ e.source) hKW hKc} = ⊤) := by
    intro KK hKKc hKKconv hKKQ hzKK hKW hKc
    have hmodel : ∀ i, Nonempty
        (((relChains (TopCat.of W) (pdRelSub W ((e ⁻¹' KK) ∩ e.source))).homology i) ≅
          ((relChains (TopCat.of (EuclideanSpace ℝ (Fin N)))
            {v : EuclideanSpace ℝ (Fin N) | v ∉ KK}).homology i)) :=
      fun i => chartConvexPair_relHomology_iso N M cc Q hQopen hQsub KK hKKc hKKQ i
    have hflat := Duality.ball_local_homology N hN KK hKKc hKKconv ⟨e (e.symm v₀), hzKK⟩
    have hflatfree := Duality.free_relChains_compl N hN KK hKKc hKKconv ⟨e (e.symm v₀), hzKK⟩
    have hfree : ∀ i, Module.Free ℤ
        ↥((relChains (TopCat.of W) (pdRelSub W ((e ⁻¹' KK) ∩ e.source))).homology i) := by
      intro i
      obtain ⟨e1⟩ := hmodel i
      haveI : Module.Free ℤ ↥((relChains (TopCat.of (EuclideanSpace ℝ (Fin N)))
          {v : EuclideanSpace ℝ (Fin N) | v ∉ KK}).homology i) := hflatfree i
      exact Module.Free.of_equiv (σ := RingHom.id ℤ) (σ' := RingHom.id ℤ)
        (uctIsoToLinearEquiv e1).symm
    have htop : Nonempty
        ((relChains (TopCat.of W) (pdRelSub W ((e ⁻¹' KK) ∩ e.source))).homology N
          ≅ ModuleCat.of ℤ ℤ) := by
      obtain ⟨e1⟩ := hmodel N
      obtain ⟨e2⟩ := hflat.2
      exact ⟨e1 ≪≫ e2⟩
    have hvan : ∀ i, i ≠ N → IsZero
        ((relChains (TopCat.of W) (pdRelSub W ((e ⁻¹' KK) ∩ e.source))).homology i) := by
      intro i hi
      obtain ⟨e1⟩ := hmodel i
      exact IsZero.of_iso (hflat.1 i hi) e1
    -- the local fundamental class generates
    have hgenM : Submodule.span ℤ
        {relLocClass M N c ((e ⁻¹' KK) ∩ e.source)} = ⊤ :=
      local_generator_convex N hN M c hc cc r hr hball KK hKKc hKKconv
        (hKKQ.trans hQball) (e.symm v₀) ⟨hzKK, hzsrc⟩
    have hgen : Submodule.span ℤ
        {localFundClass N c W hW ((e ⁻¹' KK) ∩ e.source) hKW hKc} = ⊤ := by
      have hKopen : IsOpen (((e ⁻¹' KK) ∩ e.source)ᶜ) := hKc.isClosed.isOpen_compl
      have hcov : W ∪ (((e ⁻¹' KK) ∩ e.source)ᶜ) = Set.univ := by
        rw [Set.eq_univ_iff_forall]
        intro y
        by_cases hy : y ∈ (e ⁻¹' KK) ∩ e.source
        · exact Or.inl (hKW hy)
        · exact Or.inr hy
      haveI : IsIso (HomologicalComplex.homologyMap
          (relChainsMap M W (((e ⁻¹' KK) ∩ e.source)ᶜ)) N) :=
        excision_relChainsMap_isIso M W (((e ⁻¹' KK) ∩ e.source)ᶜ) hW hKopen hcov N
      let ψ : ↥((relChains (TopCat.of W)
            (pdRelSub W ((e ⁻¹' KK) ∩ e.source))).homology N) →ₗ[ℤ]
          ↥((relChains M (((e ⁻¹' KK) ∩ e.source)ᶜ)).homology N) :=
        (HomologicalComplex.homologyMap
          (relChainsMap M W (((e ⁻¹' KK) ∩ e.source)ᶜ)) N).hom
      have hψμ : ψ (localFundClass N c W hW ((e ⁻¹' KK) ∩ e.source) hKW hKc)
          = relLocClass M N c ((e ⁻¹' KK) ∩ e.source) :=
        localFundClass_spec N c W hW ((e ⁻¹' KK) ∩ e.source) hKW hKc
      have hspanψ : Submodule.span ℤ
          {ψ (localFundClass N c W hW ((e ⁻¹' KK) ∩ e.source) hKW hKc)} = ⊤ := by
        rw [hψμ]; exact hgenM
      have hinj : Function.Injective ψ := by
        have h := (ModuleCat.mono_iff_injective
          (HomologicalComplex.homologyMap
            (relChainsMap M W (((e ⁻¹' KK) ∩ e.source)ᶜ)) N)).mp (IsIso.mono_of_iso _)
        simpa [ψ] using h
      refine le_antisymm le_top ?_
      intro v _
      have hmem : ψ v ∈ Submodule.map ψ (Submodule.span ℤ
          ({localFundClass N c W hW ((e ⁻¹' KK) ∩ e.source) hKW hKc} : Set _)) := by
        rw [Submodule.map_span, Set.image_singleton, hspanψ]
        exact Submodule.mem_top
      obtain ⟨w, hw, hwv⟩ := hmem
      have hwv' : w = v := hinj hwv
      rw [← hwv']
      exact hw
    exact ⟨hfree, htop, hvan, hgen⟩
  refine fun k m hkm => ⟨?_, ?_⟩
  · -- ## the surjectivity clause
    intro y
    by_cases hk : k = N
    · -- the top degree: the cap product with a generator is bijective
      have hK₀W : ((e ⁻¹' ({v₀} : Set (EuclideanSpace ℝ (Fin N)))) ∩ e.source) ⊆ W :=
        key_sub {v₀} (by intro v hv; rw [Set.mem_singleton_iff] at hv; rw [hv]; exact hv₀)
      have hK₀c : IsCompact ((e ⁻¹' ({v₀} : Set (EuclideanSpace ℝ (Fin N)))) ∩ e.source) :=
        key_compact {v₀} isCompact_singleton
          (by intro v hv; rw [Set.mem_singleton_iff] at hv; rw [hv]; exact hv₀)
      obtain ⟨hfree, htop, -, hgen⟩ := key {v₀} isCompact_singleton (convex_singleton v₀)
        (by intro v hv; rw [Set.mem_singleton_iff] at hv; rw [hv]; exact hv₀)
        (by rw [hez]; exact Set.mem_singleton v₀) hK₀W hK₀c
      have hbij := goodD_top_bijective (N := N) (c := c) hW hK₀W hK₀c hfree htop hgen k m hkm hk.symm
      obtain ⟨x, hx⟩ := hbij.2 y
      exact ⟨(e ⁻¹' ({v₀} : Set (EuclideanSpace ℝ (Fin N)))) ∩ e.source, hK₀W, hK₀c, x, hx⟩
    · -- the target vanishes for `k ≠ N`
      have hmpos : 0 < m := by omega
      haveI : Subsingleton ↥((singularChains ℤ (TopCat.of W)).homology m) :=
        ModuleCat.subsingleton_of_isZero (homologyContractible (X := TopCat.of W) m hmpos)
      exact ⟨∅, Set.empty_subset W, isCompact_empty, 0, Subsingleton.elim _ _⟩
  · -- ## the injectivity clause
    classical
    intro K hKW hKc x hx
    -- the enlargement: a compact convex polytope containing `e '' K ∪ {v₀}`, inside `Q`
    have himg : e '' K ⊆ Q := by
      rintro v ⟨y, hyK, rfl⟩
      exact (hKW hyK).1
    have hKtgt : K ⊆ e.source := fun y hy => (hKW hy).2
    have himgc : IsCompact (e '' K) :=
      hKc.image_of_continuousOn (e.continuousOn.mono hKtgt)
    -- a compact convex polytope around each point of `e '' K ∪ {v₀}`, inside `Q`
    have hpoint : ∀ y ∈ (e '' K ∪ ({v₀} : Set (EuclideanSpace ℝ (Fin N)))),
        ∃ u : Finset (EuclideanSpace ℝ (Fin N)),
          y ∈ interior (convexHull ℝ (u : Set (EuclideanSpace ℝ (Fin N)))) ∧
          convexHull ℝ (u : Set (EuclideanSpace ℝ (Fin N))) ⊆ Q := by
      intro y hy
      have hyQ : y ∈ Q := by
        rcases hy with hy | hy
        · exact himg hy
        · rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hv₀
      have hnbh : Q ∈ 𝓝ˢ ({y} : Set (EuclideanSpace ℝ (Fin N))) := by
        rw [mem_nhdsSet_iff_forall]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        exact hQopen.mem_nhds hyQ
      obtain ⟨u, hu₁, hu₂⟩ :=
        Convex.exists_subset_interior_convexHull_finset_of_isCompact
          (convex_singleton y) isCompact_singleton hnbh
      exact ⟨u, hu₁ (Set.mem_singleton y), hu₂⟩
    let u : EuclideanSpace ℝ (Fin N) → Finset (EuclideanSpace ℝ (Fin N)) :=
      fun y => if hy : y ∈ (e '' K ∪ ({v₀} : Set (EuclideanSpace ℝ (Fin N)))) then
        Classical.choose (hpoint y hy) else ∅
    have hu : ∀ y (hy : y ∈ (e '' K ∪ ({v₀} : Set (EuclideanSpace ℝ (Fin N))))),
        y ∈ interior (convexHull ℝ ((u y : Finset (EuclideanSpace ℝ (Fin N))) :
            Set (EuclideanSpace ℝ (Fin N)))) ∧
        convexHull ℝ ((u y : Finset (EuclideanSpace ℝ (Fin N))) :
            Set (EuclideanSpace ℝ (Fin N))) ⊆ Q := by
      intro y hy
      have hu_eq : u y = Classical.choose (hpoint y hy) := by
        dsimp only [u]
        rw [dif_pos hy]
      rw [hu_eq]
      exact Classical.choose_spec (hpoint y hy)
    have hScomp : IsCompact ((e '' K) ∪ ({v₀} : Set (EuclideanSpace ℝ (Fin N)))) :=
      himgc.union isCompact_singleton
    let fam : EuclideanSpace ℝ (Fin N) → Set (EuclideanSpace ℝ (Fin N)) :=
      fun y => if hy : y ∈ (e '' K ∪ ({v₀} : Set (EuclideanSpace ℝ (Fin N)))) then
          interior (convexHull ℝ ((u y : Finset (EuclideanSpace ℝ (Fin N))) :
            Set (EuclideanSpace ℝ (Fin N))))
        else ∅
    have hfam_pos : ∀ y (hy : y ∈ (e '' K ∪ ({v₀} : Set (EuclideanSpace ℝ (Fin N))))),
        fam y = interior (convexHull ℝ ((u y : Finset (EuclideanSpace ℝ (Fin N))) :
            Set (EuclideanSpace ℝ (Fin N)))) := by
      intro y hy; dsimp only [fam]; rw [dif_pos hy]
    have hfam_neg : ∀ y, y ∉ (e '' K ∪ ({v₀} : Set (EuclideanSpace ℝ (Fin N)))) → fam y = ∅ := by
      intro y hy; dsimp only [fam]; rw [dif_neg hy]
    obtain ⟨t, ht⟩ := hScomp.elim_finite_subcover fam
      (fun y => by
        by_cases hy : y ∈ (e '' K ∪ ({v₀} : Set (EuclideanSpace ℝ (Fin N))))
        · rw [hfam_pos y hy]; exact isOpen_interior
        · rw [hfam_neg y hy]; exact isOpen_empty)
      (fun y hy => by
        simp only [Set.mem_iUnion]
        exact ⟨y, by rw [hfam_pos y hy]; exact (hu y hy).1⟩)
    set T : Finset (EuclideanSpace ℝ (Fin N)) := t.biUnion u with hTdef
    have hTsub : (T : Set (EuclideanSpace ℝ (Fin N))) ⊆ Q := by
      intro w hw
      rw [hTdef, Finset.mem_coe, Finset.mem_biUnion] at hw
      obtain ⟨y, -, hwy⟩ := hw
      by_cases hy : y ∈ (e '' K ∪ ({v₀} : Set (EuclideanSpace ℝ (Fin N))))
      · exact (hu y hy).2 (subset_convexHull ℝ _ hwy)
      · have h0 : u y = ∅ := by dsimp only [u]; rw [dif_neg hy]
        rw [h0] at hwy
        exact absurd hwy (by simp)
    have hSsub : ((e '' K) ∪ ({v₀} : Set (EuclideanSpace ℝ (Fin N)))) ⊆
        convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin N))) := by
      intro w hw
      have h1 := ht hw
      simp only [Set.mem_iUnion] at h1
      obtain ⟨y, hyt, hwy⟩ := h1
      by_cases hy : y ∈ (e '' K ∪ ({v₀} : Set (EuclideanSpace ℝ (Fin N))))
      · have h2 : w ∈ convexHull ℝ ((u y : Finset (EuclideanSpace ℝ (Fin N))) :
            Set (EuclideanSpace ℝ (Fin N))) := by
          rw [hfam_pos y hy] at hwy
          exact interior_subset hwy
        exact convexHull_mono (fun z hz => by
          rw [hTdef, Finset.mem_coe, Finset.mem_biUnion]
          exact ⟨y, hyt, hz⟩) h2
      · rw [hfam_neg y hy] at hwy
        exact absurd hwy (by simp)
    set KK : Set (EuclideanSpace ℝ (Fin N)) :=
      convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin N))) with hKKdef
    have hKKc : IsCompact KK := by
      rw [hKKdef]
      exact Set.Finite.isCompact_convexHull ℝ (T.finite_toSet)
    have hKKconv : Convex ℝ KK := by rw [hKKdef]; exact convex_convexHull ℝ _
    have hKKQ : KK ⊆ Q := by
      rw [hKKdef]
      exact convexHull_min hTsub hQconv
    have hzKK : e (e.symm v₀) ∈ KK := by
      rw [hKKdef]
      refine hSsub (Or.inr ?_)
      rw [hez]
      exact Set.mem_singleton v₀
    have hK'eq : ((e ⁻¹' KK) ∩ e.source) ⊇ K := by
      intro y hy
      refine ⟨?_, hKtgt hy⟩
      have hmem : e y ∈ (e '' K) ∪ ({v₀} : Set (EuclideanSpace ℝ (Fin N))) :=
        Or.inl ⟨y, hy, rfl⟩
      exact hSsub hmem
    have hK'c : IsCompact ((e ⁻¹' KK) ∩ e.source) := key_compact KK hKKc hKKQ
    have hK'W : ((e ⁻¹' KK) ∩ e.source) ⊆ W := key_sub KK hKKQ
    obtain ⟨hfree, htop, hvan, hgen⟩ := key KK hKKc hKKconv hKKQ hzKK hK'W hK'c
    by_cases hk : k = N
    · have hbij := goodD_top_bijective (N := N) (c := c) hW hK'W hK'c hfree htop hgen k m hkm hk.symm
      refine ⟨(e ⁻¹' KK) ∩ e.source, hK'eq, hK'W, hK'c, ?_⟩
      have h1 : goodD N c W hW ((e ⁻¹' KK) ∩ e.source) hK'W hK'c k m hkm
          (HomologicalComplex.homologyMap
            (pdRelComplexEnlarge W hK'eq) k x) = 0 := by
        rw [pd_goodD_natural N c W hW hK'eq hKW hK'W hKc hK'c k m hkm x]
        exact hx
      refine hbij.1 ?_
      show goodD N c W hW ((e ⁻¹' KK) ∩ e.source) hK'W hK'c k m hkm
          ((HomologicalComplex.homologyMap (pdRelComplexEnlarge W hK'eq) k) x)
        = goodD N c W hW ((e ⁻¹' KK) ∩ e.source) hK'W hK'c k m hkm 0
      rw [h1]
      simp only [goodD, map_zero, LinearMap.zero_apply]
    · haveI : Subsingleton ↥((relComplex ℤ (TopCat.of W)
          (pdRelSub W ((e ⁻¹' KK) ∩ e.source))).homology k) := by
        obtain ⟨e1⟩ := relCohomologyDual (TopCat.of W)
          (pdRelSub W ((e ⁻¹' KK) ∩ e.source)) hfree k
        haveI : Subsingleton ↥(ModuleCat.of ℤ
            (↥((relChains (TopCat.of W)
              (pdRelSub W ((e ⁻¹' KK) ∩ e.source))).homology k) →ₗ[ℤ] ℤ)) := by
          haveI : Subsingleton ↥((relChains (TopCat.of W)
              (pdRelSub W ((e ⁻¹' KK) ∩ e.source))).homology k) :=
            ModuleCat.subsingleton_of_isZero (hvan k hk)
          refine ⟨fun f g => LinearMap.ext fun mm => ?_⟩
          rw [Subsingleton.elim mm 0, map_zero, map_zero]
        exact ((ConcreteCategory.bijective_of_isIso e1.hom).1).subsingleton
      exact ⟨(e ⁻¹' KK) ∩ e.source, hK'eq, hK'W, hK'c, Subsingleton.elim _ _⟩

end

end Work.Cohomology

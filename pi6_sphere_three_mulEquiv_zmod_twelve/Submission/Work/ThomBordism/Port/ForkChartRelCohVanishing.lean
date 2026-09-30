
-- Copied verbatim from `Submission.Work.Projective.GoodCp2.fork.chart_relCohomology_vanishing_of_compact`, with imports re-routed:
-- the fork's own copy of `capped_localDegree_generator` is a *verbatim* duplicate of
-- `Submission.Work.Cohomology.capped_localDegree_generator`, and the latter is in the import
-- closure of `Submission.Work.ThomBordism.Interface` (via the Milnor chapter), so the two
-- cannot be combined: the import is re-routed to the original.  All declarations keep their
-- original names and proofs.
import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.ThomBordism.Port.ForkIsZeroKcompactHigh
import Submission.Work.Cohomology.sphereCohomologyZero
import Submission.Work.Cohomology.Duality.convex_compl_sphere
import Submission.Work.Cohomology.chartConvexPair_relHomology_iso
import Submission.Work.Cohomology.Duality.ball_local_homology
import Submission.Work.Cohomology.Duality.euclidean_convex_local_cohomology
import Submission.Work.Cohomology.relCohomologyDual
import Submission.Work.Cohomology.relCohomology_univ_vanishing
import Submission.Work.Cohomology.relComplex_empty_homology_iso
import Submission.Work.Cohomology.contractible
import Submission.Work.Cohomology.homology_biprod_iso
import Submission.Work.Cohomology.pd_ab_clean
import Submission.Work.Cohomology.pdABCoh_quasiIso

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option synthInstance.maxHeartbeats 400000

/-!
# Vanishing of `H^k(I, I∖K')` for `k > n`, `I` an open subset of a chart

For a charted topological `n`-manifold `M`, an open set `I ⊆ M` contained in the source of a chart,
a compact `K ⊆ I` and a degree `k > n`, there is a compact `K'` with `K ⊆ K' ⊆ I` and
`H^k(I, I∖K') = 0`.

The proof is in four steps.

* `coordPiece_relCohomology_vanishing`: the base case, a single *convex* coordinate piece
  `K = e⁻¹' P ∩ e.source` with `P` compact convex inside the chart: the chart identifies the pair
  with `(ℝⁿ, ℝⁿ∖P)` (`chartConvexPair_relHomology_iso`), whose relative homology is `0` off degree
  `n` and free (`Duality.ball_local_homology`, `Duality.free_relChains_compl`), and the universal
  coefficient theorem (`relCohomologyDual`) identifies `H^k` with the dual of `H_k`.
* `relCohomology_union_step`: the excluded-set form of the Mayer–Vietoris (Hatcher 3.36) step, from
  the "A+B" short exact sequence of cochain complexes (`pd_ab_clean`, in the clash-free namespace
  `Work.Cohomology.PDABClean`) together with the identification `C^*(X,A+B) ≃ C^*(X,A∪B)`
  (`pdABCoh_quasiIso`).
* `finite_union_pieces_vanishing`: by induction, the union of any finite family of convex
  coordinate pieces has the vanishing property.
* `exists_finite_closedBall_cover`: a compact subset of an open subset of `ℝⁿ` is covered by
  finitely many closed balls contained in that open set.

The main theorem is the assembly.
-/

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-! ## Elementary set-theoretic bookkeeping -/

/-- The complement of the empty set inside `W` is everything. -/
lemma pdRelSub_empty_eq_univ {M : TopCat} (W : Set M) : pdRelSub W (∅ : Set M) = Set.univ := by
  ext y
  simp [pdRelSub]

/-- The complement of `K ∩ L` inside `W` is the union of the complements. -/
lemma pdRelSub_union_eq {M : TopCat} (W K L : Set M) :
    pdRelSub W K ∪ pdRelSub W L = pdRelSub W (K ∩ L) := by
  ext y
  simp only [Set.mem_union, pdRelSub, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_inter_iff]
  tauto

/-- The complement of `K ∪ L` inside `W` is the intersection of the complements. -/
lemma pdRelSub_inter_eq {M : TopCat} (W K L : Set M) :
    pdRelSub W K ∩ pdRelSub W L = pdRelSub W (K ∪ L) := by
  ext y
  simp only [Set.mem_inter_iff, pdRelSub, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_union]
  tauto

/-- Preimages of unions of coordinate pieces, intersected with the source. -/
lemma kp_union {M : TopCat} {E : Type*} [TopologicalSpace E] (e : OpenPartialHomeomorph M E) (A B : Set E) :
    ((e ⁻¹' A) ∩ e.source) ∪ ((e ⁻¹' B) ∩ e.source) = (e ⁻¹' (A ∪ B)) ∩ e.source := by
  ext x
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_preimage]
  tauto

/-- Preimages of intersections of coordinate pieces, intersected with the source. -/
lemma kp_inter {M : TopCat} {E : Type*} [TopologicalSpace E] (e : OpenPartialHomeomorph M E) (A B : Set E) :
    ((e ⁻¹' A) ∩ e.source) ∩ ((e ⁻¹' B) ∩ e.source) = (e ⁻¹' (A ∩ B)) ∩ e.source := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  tauto

/-- The preimage of a finite union, intersected with the source, is the union of the pieces. -/
lemma preimage_biUnion_inter {M : TopCat} {E : Type*} [TopologicalSpace E] (e : OpenPartialHomeomorph M E)
    {ι : Type} (s : Finset ι) (P : ι → Set E) :
    (e ⁻¹' (⋃ i ∈ s, P i)) ∩ e.source = ⋃ i ∈ s, ((e ⁻¹' P i) ∩ e.source) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨i, hi, hxi⟩, hxs⟩
    exact ⟨i, hi, hxi, hxs⟩
  · rintro ⟨i, hi, hxi, hxs⟩
    exact ⟨⟨i, hi, hxi⟩, hxs⟩

/-- Inserting a piece into the union. -/
lemma biUnion_insert_eq {E ι : Type} [DecidableEq ι] (a : ι) (s : Finset ι) (P : ι → Set E) :
    (⋃ i ∈ insert a s, P i) = (⋃ i ∈ s, P i) ∪ P a := by
  ext v
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i, hi, hvi⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Or.inr hvi
    · exact Or.inl ⟨i, hi, hvi⟩
  · rintro (⟨i, hi, hvi⟩ | hva)
    · exact ⟨i, Finset.mem_insert_of_mem hi, hvi⟩
    · exact ⟨a, Finset.mem_insert_self a s, hva⟩

/-- The intersection of a coordinate piece with a piece over the intersection of the unions. -/
lemma kp_inter_biUnion {M : TopCat} {E : Type*} [TopologicalSpace E] (e : OpenPartialHomeomorph M E)
    {ι : Type} (s : Finset ι) (P : ι → Set E) (B : Set E) :
    ((e ⁻¹' (⋃ i ∈ s, P i)) ∩ e.source) ∩ ((e ⁻¹' B) ∩ e.source)
      = (e ⁻¹' (⋃ i ∈ s, P i ∩ B)) ∩ e.source := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨⟨i, hi, hxi⟩, hxs⟩, ⟨hxB, -⟩⟩
    exact ⟨⟨i, hi, hxi, hxB⟩, hxs⟩
  · rintro ⟨⟨i, hi, hxi, hxB⟩, hxs⟩
    exact ⟨⟨⟨i, hi, hxi⟩, hxs⟩, ⟨hxB, hxs⟩⟩

/-- The union of a coordinate piece with a piece over the union of the family. -/
lemma kp_union_biUnion_insert {M : TopCat} {E : Type*} [TopologicalSpace E]
    (e : OpenPartialHomeomorph M E) {ι : Type} [DecidableEq ι] (a : ι) (s : Finset ι)
    (P : ι → Set E) :
    ((e ⁻¹' (⋃ i ∈ s, P i)) ∩ e.source) ∪ ((e ⁻¹' P a) ∩ e.source)
      = (e ⁻¹' (⋃ i ∈ insert a s, P i)) ∩ e.source := by
  ext x
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion]
  constructor
  · rintro (⟨⟨i, hi, hxi⟩, hxs⟩ | ⟨hxa, hxs⟩)
    · exact ⟨⟨i, Finset.mem_insert_of_mem hi, hxi⟩, hxs⟩
    · exact ⟨⟨a, Finset.mem_insert_self a s, hxa⟩, hxs⟩
  · rintro ⟨⟨i, hi, hxi⟩, hxs⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Or.inr ⟨hxi, hxs⟩
    · exact Or.inl ⟨⟨i, hi, hxi⟩, hxs⟩

/-! ## Transport of vanishing along set equalities -/

/-- Vanishing of a relative cohomology group is invariant under replacing the excluded set by an
equal set. -/
lemma subsingleton_relComplex_of_eq {R : Type} [CommRing R] {X : TopCat} {A B : Set X} (h : A = B)
    {k : ℕ} (hA : Subsingleton ((relComplex R X A).homology k)) :
    Subsingleton ((relComplex R X B).homology k) := by
  rw [h] at hA
  exact hA

/-- Vanishing of a relative cohomology group is invariant under replacing the ambient subset (hence
the ambient space) by an equal set. -/
lemma subsingleton_relComplex_subtype_of_eq {M : TopCat} {W I : Set M} (h : W = I) (K : Set M)
    (k : ℕ) (hW : Subsingleton ((relComplex ℤ (TopCat.of W) (pdRelSub W K)).homology k)) :
    Subsingleton ((relComplex ℤ (TopCat.of I) (pdRelSub I K)).homology k) := by
  subst h
  exact hW

/-- A biproduct of two zero modules is a zero module. -/
lemma subsingleton_biprod {R : Type} [Ring R] (M N : ModuleCat R) [Subsingleton ↥M]
    [Subsingleton ↥N] : Subsingleton ↥(M ⊞ N) := by
  haveI : Subsingleton (↥M × ↥N) := inferInstance
  exact ⟨fun a b => (ConcreteCategory.bijective_of_isIso (ModuleCat.biprodIsoProd M N).hom).1
    (Subsingleton.elim _ _)⟩

/-! ## Compactness of coordinate pieces -/

/-- A coordinate piece `e ⁻¹' S ∩ e.source` over a compact `S` is compact. -/
lemma isCompact_kp {M : TopCat} {E : Type*} [TopologicalSpace E] (e : OpenPartialHomeomorph M E)
    {S : Set E} (hS : IsCompact S) (hSt : S ⊆ e.target) :
    IsCompact ((e ⁻¹' S) ∩ e.source) := by
  have heq : (e ⁻¹' S) ∩ e.source = e.symm '' S := by
    rw [Set.inter_comm, ← OpenPartialHomeomorph.symm_image_eq_source_inter_preimage e hSt]
  rw [heq]
  exact hS.image_of_continuousOn (e.continuousOn_symm.mono hSt)

/-- A finite union of compact coordinate pieces is compact. -/
lemma isCompact_kp_biUnion {M : TopCat} {E : Type*} [TopologicalSpace E]
    (e : OpenPartialHomeomorph M E) {ι : Type} (s : Finset ι) (P : ι → Set E)
    (hPc : ∀ i ∈ s, IsCompact (P i)) (hPt : ∀ i ∈ s, P i ⊆ e.target) :
    IsCompact ((e ⁻¹' (⋃ i ∈ s, P i)) ∩ e.source) := by
  rw [preimage_biUnion_inter]
  exact Finset.isCompact_biUnion s (fun i hi => isCompact_kp e (hPc i hi) (hPt i hi))

/-! ## The base case: a single convex coordinate piece -/

theorem coordPiece_relCohomology_vanishing {N : ℕ} (hN : 1 ≤ N) {M : TopCat} [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M] (cc : M) :
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)) := chartAt (EuclideanSpace ℝ (Fin N)) cc
    (Q : Set (EuclideanSpace ℝ (Fin N))) → IsOpen Q → Q ⊆ e.target →
    (P : Set (EuclideanSpace ℝ (Fin N))) → IsCompact P → Convex ℝ P → P ⊆ Q →
    let W : Set M := (e ⁻¹' Q) ∩ e.source
    let K : Set M := (e ⁻¹' P) ∩ e.source
    ∀ k, k ≠ N → Subsingleton ((relComplex ℤ (TopCat.of W) (pdRelSub W K)).homology k) := by
  intro e Q hQ hQsub P hPc hPconv hPQ W K
  by_cases hne : P.Nonempty
  · have hmodel : ∀ i, Nonempty
        (((relChains (TopCat.of W) (pdRelSub W K)).homology i) ≅
          ((relChains (TopCat.of (EuclideanSpace ℝ (Fin N)))
            {v : EuclideanSpace ℝ (Fin N) | v ∉ P}).homology i)) :=
      fun i => chartConvexPair_relHomology_iso N M cc Q hQ hQsub P hPc hPQ i
    have hflat := Duality.ball_local_homology N hN P hPc hPconv hne
    have hflatfree := Duality.free_relChains_compl N hN P hPc hPconv hne
    have hfree : ∀ i, Module.Free ℤ ↥((relChains (TopCat.of W) (pdRelSub W K)).homology i) := by
      intro i
      obtain ⟨e1⟩ := hmodel i
      haveI : Module.Free ℤ ↥((relChains (TopCat.of (EuclideanSpace ℝ (Fin N)))
          {v : EuclideanSpace ℝ (Fin N) | v ∉ P}).homology i) := hflatfree i
      exact Module.Free.of_equiv (σ := RingHom.id ℤ) (σ' := RingHom.id ℤ)
        (uctIsoToLinearEquiv e1).symm
    have hvan : ∀ i, i ≠ N → IsZero ((relChains (TopCat.of W) (pdRelSub W K)).homology i) := by
      intro i hi
      obtain ⟨e1⟩ := hmodel i
      exact IsZero.of_iso (hflat.1 i hi) e1
    intro k hk
    obtain ⟨e1⟩ := relCohomologyDual (TopCat.of W) (pdRelSub W K) hfree k
    haveI : Subsingleton ↥((relChains (TopCat.of W) (pdRelSub W K)).homology k) :=
      ModuleCat.subsingleton_of_isZero (hvan k hk)
    haveI : Subsingleton ↥(ModuleCat.of ℤ (↥((relChains (TopCat.of W)
        (pdRelSub W K)).homology k) →ₗ[ℤ] ℤ)) :=
      ⟨fun f g => LinearMap.ext fun m => by
        rw [Subsingleton.elim m 0, map_zero, map_zero]⟩
    exact ((ConcreteCategory.bijective_of_isIso e1.hom).1).subsingleton
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    intro k _
    have hKeq : K = (∅ : Set M) := by
      show (e ⁻¹' P) ∩ e.source = ∅
      rw [hne]
      simp
    rw [hKeq, pdRelSub_empty_eq_univ]
    exact relCohomology_univ_vanishing (TopCat.of W) k

/-! ## The Mayer--Vietoris union step -/

theorem relCohomology_union_step {M : TopCat} [T2Space M] (W K L : Set M)
    (hKc : IsCompact K) (hLc : IsCompact L) (k : ℕ)
    (hK0 : Subsingleton ((relComplex ℤ (TopCat.of W) (pdRelSub W K)).homology k))
    (hL0 : Subsingleton ((relComplex ℤ (TopCat.of W) (pdRelSub W L)).homology k))
    (hKL : Subsingleton ((relComplex ℤ (TopCat.of W) (pdRelSub W (K ∩ L))).homology (k + 1))) :
    Subsingleton ((relComplex ℤ (TopCat.of W) (pdRelSub W (K ∪ L))).homology k) := by
  have hA : IsOpen (pdRelSub W K) := (hKc.isClosed.isOpen_compl).preimage continuous_subtype_val
  have hB : IsOpen (pdRelSub W L) := (hLc.isClosed.isOpen_compl).preimage continuous_subtype_val
  haveI hZr : IsZero ((relComplex ℤ (TopCat.of W) (pdRelSub W K)).homology k) :=
    ModuleCat.isZero_iff_subsingleton.mpr hK0
  haveI hZs : IsZero ((relComplex ℤ (TopCat.of W) (pdRelSub W L)).homology k) :=
    ModuleCat.isZero_iff_subsingleton.mpr hL0
  have hbip : IsZero ((relComplex ℤ (TopCat.of W) (pdRelSub W K) ⊞
      relComplex ℤ (TopCat.of W) (pdRelSub W L)).homology k) := by
    obtain ⟨e, -, -⟩ := homology_biprod_iso (relComplex ℤ (TopCat.of W) (pdRelSub W K))
      (relComplex ℤ (TopCat.of W) (pdRelSub W L)) k
    have hpair : IsZero ((relComplex ℤ (TopCat.of W) (pdRelSub W K)).homology k ⊞
        (relComplex ℤ (TopCat.of W) (pdRelSub W L)).homology k) :=
      ModuleCat.isZero_iff_subsingleton.mpr (subsingleton_biprod _ _)
    exact IsZero.of_iso hpair e
  have hex3 : (ShortComplex.mk
      (HomologicalComplex.homologyMap (PDABClean.pdABg (TopCat.of W) (pdRelSub W K)
        (pdRelSub W L)) k)
      (PDABClean.pdABδ (TopCat.of W) (pdRelSub W K) (pdRelSub W L) k)
      (PDABClean.pdAB_comp_δ (TopCat.of W) (pdRelSub W K) (pdRelSub W L) k)).Exact :=
    PDABClean.pdAB_exact₃ (TopCat.of W) (pdRelSub W K) (pdRelSub W L) k
  have hrange := ShortComplex.Exact.moduleCat_range_eq_ker hex3
  have hg0 : HomologicalComplex.homologyMap (PDABClean.pdABg (TopCat.of W) (pdRelSub W K)
      (pdRelSub W L)) k = 0 := IsZero.eq_zero_of_src hbip _
  have hker : (ModuleCat.Hom.hom (PDABClean.pdABδ (TopCat.of W) (pdRelSub W K)
      (pdRelSub W L) k)).ker = ⊥ := by
    rw [← hrange]
    simp only [hg0]
    exact LinearMap.range_zero
  have hinj : Function.Injective ⇑(ModuleCat.Hom.hom (PDABClean.pdABδ (TopCat.of W)
      (pdRelSub W K) (pdRelSub W L) k)) := LinearMap.ker_eq_bot.mp hker
  have hAU : pdRelSub W K ∪ pdRelSub W L = pdRelSub W (K ∩ L) := pdRelSub_union_eq W K L
  haveI : Subsingleton ↥((relComplex ℤ (TopCat.of W)
      (pdRelSub W K ∪ pdRelSub W L)).homology (k + 1)) :=
    subsingleton_relComplex_of_eq hAU.symm hKL
  haveI : IsZero ((relComplex ℤ (TopCat.of W)
      (pdRelSub W K ∪ pdRelSub W L)).homology (k + 1)) :=
    ModuleCat.isZero_iff_subsingleton.mpr this
  haveI hqiso : IsIso (HomologicalComplex.homologyMap
      (pdABInclRel (TopCat.of W) (pdRelSub W K) (pdRelSub W L)) (k + 1)) :=
    pdABCoh_quasiIso hA hB (k + 1)
  haveI : IsZero ((pdABCoh (TopCat.of W) (pdRelSub W K) (pdRelSub W L)).homology (k + 1)) :=
    IsZero.of_iso this (asIso (HomologicalComplex.homologyMap
      (pdABInclRel (TopCat.of W) (pdRelSub W K) (pdRelSub W L)) (k + 1))).symm
  haveI : Subsingleton ↥((pdABCoh (TopCat.of W) (pdRelSub W K) (pdRelSub W L)).homology
      (k + 1)) := ModuleCat.subsingleton_of_isZero this
  have hmain : Subsingleton ↥((relComplex ℤ (TopCat.of W)
      (pdRelSub W K ∩ pdRelSub W L)).homology k) :=
    ⟨fun a b => hinj (Subsingleton.elim _ _)⟩
  have hAB : pdRelSub W K ∩ pdRelSub W L = pdRelSub W (K ∪ L) := pdRelSub_inter_eq W K L
  exact subsingleton_relComplex_of_eq hAB hmain

/-! ## Finite unions of convex coordinate pieces -/

set_option maxHeartbeats 2000000 in
theorem finite_union_pieces_vanishing {N : ℕ} (hN : 1 ≤ N) {M : TopCat} [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M] (cc : M)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)))
    (he : e = chartAt (EuclideanSpace ℝ (Fin N)) cc) (I : Set M)
    (hIsrc : I ⊆ e.source) (hIopen : IsOpen I) :
    (ι : Type) → [DecidableEq ι] → (s : Finset ι) → (P : ι → Set (EuclideanSpace ℝ (Fin N))) →
    (∀ i ∈ s, IsCompact (P i)) → (∀ i ∈ s, Convex ℝ (P i)) →
    (∀ i ∈ s, P i ⊆ e '' I) →
    ∀ k, N < k → Subsingleton ((relComplex ℤ (TopCat.of I)
      (pdRelSub I ((e ⁻¹' (⋃ i ∈ s, P i)) ∩ e.source))).homology k) := by
  intro ι _ s
  induction s using Finset.induction_on with
  | empty =>
    intro P _ _ _ k _
    have h1 : (e ⁻¹' (⋃ i ∈ (∅ : Finset ι), P i)) ∩ e.source = (∅ : Set M) := by simp
    rw [h1, pdRelSub_empty_eq_univ]
    exact relCohomology_univ_vanishing (TopCat.of I) k
  | insert a s has ih =>
    intro P hPc hPcvx hPI k hk
    have hIimg : e '' I ⊆ e.target := fun v hv => by
      obtain ⟨x, hx, rfl⟩ := hv
      exact e.map_source (hIsrc hx)
    have hPct : ∀ i ∈ s, P i ⊆ e.target :=
      fun i hi => (hPI i (Finset.mem_insert_of_mem hi)).trans hIimg
    let K : Set M := (e ⁻¹' (⋃ i ∈ s, P i)) ∩ e.source
    let L : Set M := (e ⁻¹' P a) ∩ e.source
    have hKc : IsCompact K :=
      isCompact_kp_biUnion e s P (fun i hi => hPc i (Finset.mem_insert_of_mem hi)) hPct
    have hLc : IsCompact L :=
      isCompact_kp e (hPc a (Finset.mem_insert_self a s))
        ((hPI a (Finset.mem_insert_self a s)).trans hIimg)
    have hK0 : Subsingleton ((relComplex ℤ (TopCat.of I) (pdRelSub I K)).homology k) :=
      ih P (fun i hi => hPc i (Finset.mem_insert_of_mem hi))
        (fun i hi => hPcvx i (Finset.mem_insert_of_mem hi))
        (fun i hi => hPI i (Finset.mem_insert_of_mem hi)) k hk
    have hL0 : Subsingleton ((relComplex ℤ (TopCat.of I) (pdRelSub I L)).homology k) := by
      have hQsub : e '' I ⊆ (chartAt (EuclideanSpace ℝ (Fin N)) cc).target := by
        rw [← he]
        exact hIimg
      have h := coordPiece_relCohomology_vanishing (N := N) hN cc (e '' I)
        (e.isOpen_image_of_subset_source hIopen hIsrc) hQsub (P a)
        (hPc a (Finset.mem_insert_self a s)) (hPcvx a (Finset.mem_insert_self a s))
        (hPI a (Finset.mem_insert_self a s)) k (by omega)
      rw [← he] at h
      have hW : (e ⁻¹' (e '' I)) ∩ e.source = I := by
        ext x
        constructor
        · rintro ⟨⟨y, hy, hyx⟩, hxs⟩
          have hyx' : y = x := e.toPartialEquiv.injOn (hIsrc hy) hxs hyx
          rw [← hyx']
          exact hy
        · intro hx
          exact ⟨⟨x, hx, rfl⟩, hIsrc hx⟩
      exact subsingleton_relComplex_subtype_of_eq hW L k h
    have hKL : Subsingleton ((relComplex ℤ (TopCat.of I) (pdRelSub I (K ∩ L))).homology (k + 1)) := by
      have h := ih (fun i => P i ∩ P a)
        (fun i hi => (hPc i (Finset.mem_insert_of_mem hi)).inter
          (hPc a (Finset.mem_insert_self a s)))
        (fun i hi => (hPcvx i (Finset.mem_insert_of_mem hi)).inter
          (hPcvx a (Finset.mem_insert_self a s)))
        (fun i hi => Set.inter_subset_left.trans (hPI i (Finset.mem_insert_of_mem hi)))
        (k + 1) (by omega)
      rw [(kp_inter_biUnion e s P (P a)).symm] at h
      exact h
    have hmain := relCohomology_union_step I K L hKc hLc k hK0 hL0 hKL
    rw [kp_union_biUnion_insert e a s P] at hmain
    exact hmain

/-! ## A finite closed-ball cover of a compact subset of an open set -/

theorem exists_finite_closedBall_cover (N : ℕ) {J : Set (EuclideanSpace ℝ (Fin N))} (hJ : IsOpen J)
    {L : Set (EuclideanSpace ℝ (Fin N))} (hLc : IsCompact L) (hLJ : L ⊆ J) :
    ∃ (r : ℝ) (t : Finset ↥L), 0 < r ∧
      L ⊆ ⋃ x ∈ t, Metric.closedBall (x : EuclideanSpace ℝ (Fin N)) r ∧
      (∀ x ∈ t, Metric.closedBall (x : EuclideanSpace ℝ (Fin N)) r ⊆ J) := by
  obtain ⟨δ, hδ, hδJ⟩ := hLc.exists_thickening_subset_open hJ hLJ
  have hr : 0 < δ / 2 := by linarith
  have hcov : L ⊆ ⋃ x : ↥L, Metric.ball (x : EuclideanSpace ℝ (Fin N)) (δ / 2) := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self hr⟩
  obtain ⟨t, ht⟩ := hLc.elim_finite_subcover
    (fun x : ↥L => Metric.ball (x : EuclideanSpace ℝ (Fin N)) (δ / 2))
    (fun _ => Metric.isOpen_ball) hcov
  refine ⟨δ / 2, t, hr, ?_, ?_⟩
  · intro y hy
    have h1 : y ∈ ⋃ x ∈ t, Metric.ball (x : EuclideanSpace ℝ (Fin N)) (δ / 2) := ht hy
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp h1
    exact Set.mem_iUnion₂.mpr ⟨i, hi, Metric.ball_subset_closedBall hyi⟩
  · intro x _ y hy
    have h1 : dist y (x : EuclideanSpace ℝ (Fin N)) ≤ δ / 2 := Metric.mem_closedBall.mp hy
    have h2 : dist (x : EuclideanSpace ℝ (Fin N)) y ≤ δ / 2 := by
      simpa only [dist_comm] using h1
    exact hδJ (Metric.mem_thickening_iff.mpr ⟨(x : EuclideanSpace ℝ (Fin N)), x.2,
      by linarith⟩)

/-! ## The main theorem -/

theorem chart_relCohomology_vanishing_of_compact {M : TopCat} [T2Space M] {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (c₀ : M) (I : Set M) (hI : I ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) c₀).source) (hIopen : IsOpen I) (k : ℕ) (hk : n < k) (K : Set M) (hK : K ⊆ I) (hKc : IsCompact K) : ∃ K' : Set M, K ⊆ K' ∧ K' ⊆ I ∧ IsCompact K' ∧ Subsingleton ((Work.Cohomology.relComplex ℤ (TopCat.of I) (Work.Cohomology.pdRelSub I K')).homology k) := by
  classical
  by_cases hn0 : n = 0
  · subst hn0
    haveI hI_sub : Subsingleton ↥I := by
      haveI htgt : Subsingleton ↥((chartAt (EuclideanSpace ℝ (Fin 0)) c₀).target) :=
        ⟨fun x y => Subtype.ext (Subsingleton.elim x.1 y.1)⟩
      haveI hsrc : Subsingleton ↥((chartAt (EuclideanSpace ℝ (Fin 0)) c₀).source) :=
        ⟨fun x y => (chartAt (EuclideanSpace ℝ (Fin 0)) c₀).toHomeomorphSourceTarget.injective
          (Subsingleton.elim _ _)⟩
      exact ⟨fun x y => Subtype.ext (congrArg
        (fun z : ↥((chartAt (EuclideanSpace ℝ (Fin 0)) c₀).source) => (z : M))
        (Subsingleton.elim (α := ↥((chartAt (EuclideanSpace ℝ (Fin 0)) c₀).source))
          ⟨x.1, hI x.2⟩ ⟨y.1, hI y.2⟩))⟩
    rcases I.eq_empty_or_nonempty with hIe | ⟨y, hy⟩
    · rw [hIe] at hK
      refine ⟨∅, hK, Set.empty_subset _, isCompact_empty, ?_⟩
      rw [pdRelSub_empty_eq_univ]
      exact relCohomology_univ_vanishing (TopCat.of I) k
    · have hIeq : I = {y} := Set.eq_singleton_iff_unique_mem.mpr
        ⟨hy, fun z hz => congrArg Subtype.val (Subsingleton.elim (α := ↥I) ⟨z, hz⟩ ⟨y, hy⟩)⟩
      refine ⟨I, hK, subset_rfl, ?_, ?_⟩
      · rw [hIeq]
        exact isCompact_singleton
      · have hpdeq : pdRelSub I I = (∅ : Set ↥I) := by
          ext z
          simp only [pdRelSub, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_empty_iff_false,
            iff_false, not_not]
          exact z.2
        rw [hpdeq]
        haveI hne : Nonempty ↥I := ⟨⟨y, hy⟩⟩
        haveI hct : ContractibleSpace ↥I := inferInstance
        haveI hiso : IsIso (HomologicalComplex.homologyMap
            (relIncl ℤ (TopCat.of ↥I) (∅ : Set ↥I)) k) :=
          relComplex_empty_homology_iso (TopCat.of ↥I) k
        have hk1 : 1 ≤ k := by omega
        haveI hZ : IsZero ((singularCochainComplex ℤ (TopCat.of ↥I)).homology k) := by
          have h := contractible ℤ (TopCat.of ↥I) (k - 1)
          rwa [show (k - 1) + 1 = k from by omega] at h
        haveI : IsZero ((relComplex ℤ (TopCat.of ↥I) (∅ : Set ↥I)).homology k) :=
          IsZero.of_iso hZ (asIso (HomologicalComplex.homologyMap
            (relIncl ℤ (TopCat.of ↥I) (∅ : Set ↥I)) k))
        exact ModuleCat.subsingleton_of_isZero this
  · have hN : 1 ≤ n := by omega
    set e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
      chartAt (EuclideanSpace ℝ (Fin n)) c₀ with he
    have hJopen : IsOpen (e '' I) := e.isOpen_image_of_subset_source hIopen hI
    have himgK : e '' K ⊆ e '' I := Set.image_mono hK
    have hLc : IsCompact (e '' K) := hKc.image_of_continuousOn (e.continuousOn.mono (hK.trans hI))
    obtain ⟨r, t, hr, hcover, htJ⟩ := exists_finite_closedBall_cover n hJopen hLc himgK
    let P : ↥(e '' K) → Set (EuclideanSpace ℝ (Fin n)) :=
      fun x => Metric.closedBall (x : EuclideanSpace ℝ (Fin n)) r
    have hPc : ∀ i ∈ t, IsCompact (P i) := fun i _ => isCompact_closedBall (i : EuclideanSpace ℝ (Fin n)) r
    have hPcvx : ∀ i ∈ t, Convex ℝ (P i) := fun i _ => convex_closedBall (i : EuclideanSpace ℝ (Fin n)) r
    have hPI : ∀ i ∈ t, P i ⊆ e '' I := fun i hi => htJ i hi
    refine ⟨(e ⁻¹' (⋃ i ∈ t, P i)) ∩ e.source, ?_, ?_, ?_, ?_⟩
    · intro x hx
      have h1 : e x ∈ ⋃ i ∈ t, P i := hcover ⟨x, hx, rfl⟩
      exact ⟨h1, hI (hK hx)⟩
    · rintro x ⟨hx1, hxs⟩
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx1
      obtain ⟨z, hzI, hzx⟩ := hPI i hi hxi
      have hzx' : z = x := e.toPartialEquiv.injOn (hI hzI) hxs hzx
      rw [← hzx']
      exact hzI
    · exact isCompact_kp_biUnion e t P hPc (fun i hi => (hPI i hi).trans
        (fun v hv => by obtain ⟨x, hx, rfl⟩ := hv; exact e.map_source (hI hx)))
    · exact finite_union_pieces_vanishing hN c₀ e rfl I hI hIopen (↥(e '' K)) t P hPc hPcvx
        hPI k hk

end

end Work.Cohomology

import Mathlib
import Submission.Work.Compact.Noncompact.Good
import Submission.Work.Compact.Noncompact.mem_suppS_iff_of_expansion

/-!
# Covering a compact set by Euclidean balls while keeping a chain off the closed balls

Let `M` be a topological manifold modelled on `EuclideanSpace ℝ (Fin n)`, `e` a chart of `M`,
`A ⊆ e.source` compact, and `c ∈ suppS (Aᶜ) k` a singular `k`-chain supported away from `A`.

The lemma produces finitely many Euclidean balls `ball (y i) (r i)` whose *closed* balls
`closedBall (y i) (r i)` still lie in `e.target` and are disjoint from the support of `c`, and whose
open balls cover `A`.  Equivalently, the support of `c` is still contained in the complement of the
union of the closed balls.

The mathematical content is the following.  By `mem_suppS_iff_of_expansion`, `c` is a finite sum of
generators whose simplices have image in `Aᶜ`; the union `K` of those (compact) images is therefore
compact and disjoint from the compact set `A`.  Being compact in a Hausdorff space, `K` is closed,
so every `a ∈ A` has an open neighbourhood `W ⊆ Kᶜ`; shrinking a Euclidean ball around `a` inside
`W` in the chart `e` yields the required radius.  Compactness of `A` makes finitely many of them
suffice.
-/

namespace Work.Compact.Noncompact

open CategoryTheory AlgebraicTopology

noncomputable section

set_option maxHeartbeats 1000000

/-- The image of a singular simplex is compact. -/
lemma isCompact_SimplexSet {X : TopCat} {k : ℕ} (σ : SimplexT X k) :
    IsCompact (SimplexSet σ) := by
  have : CompactSpace (Convexity.StdSimplex ℝ (Fin (k + 1))) :=
    Convexity.StdSimplex.compactSpace ℝ (Fin (k + 1))
  rw [SimplexSet]
  exact isCompact_range
    (Work.Homology.toSSetObjEquiv' X (Opposite.op (SimplexCategory.mk k)) σ).continuous

/-- Around every point of the source of a chart `e` one finds a Euclidean closed ball, contained in
`e.target`, whose `e`-preimage lies in any prescribed open neighbourhood.

More precisely: if `a ∈ e.source` and `W` is an open neighbourhood of `a`, then there is `ε > 0`
with `e.source ∩ e ⁻¹' closedBall (e a) ε ⊆ W`. -/
lemma exists_closedBall_subset_of_open {M : Type} [TopologicalSpace M] {n : ℕ}
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) {a : M} (ha : a ∈ e.source)
    {W : Set M} (hW : IsOpen W) (haW : a ∈ W) :
    ∃ ε : ℝ, 0 < ε ∧ e.source ∩ e ⁻¹' Metric.closedBall (e a) ε ⊆ W := by
  have hU : IsOpen (e '' (e.source ∩ W)) := e.isOpen_image_source_inter hW
  have hea : e a ∈ e '' (e.source ∩ W) := ⟨a, ⟨ha, haW⟩, rfl⟩
  obtain ⟨η, hηpos, hη⟩ := Metric.isOpen_iff.mp hU (e a) hea
  refine ⟨η / 2, half_pos hηpos, ?_⟩
  rintro z ⟨hzs, hz⟩
  have hmem : e z ∈ e '' (e.source ∩ W) :=
    hη (Metric.closedBall_subset_ball (by linarith) hz)
  obtain ⟨w, hw, hwe⟩ := hmem
  have hzw : z = w := e.injOn hzs hw.1 hwe.symm
  rw [hzw]
  exact hw.2

/-- Every point of the source of a chart `e` has a Euclidean closed ball around its image, contained
in `e.target`. -/
lemma exists_closedBall_subset_target {M : Type} [TopologicalSpace M] {n : ℕ}
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) {a : M} (ha : a ∈ e.source) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.closedBall (e a) δ ⊆ e.target := by
  obtain ⟨η, hηpos, hη⟩ := Metric.isOpen_iff.mp e.open_target (e a) (e.map_source ha)
  exact ⟨η / 2, half_pos hηpos, (Metric.closedBall_subset_ball (by linarith)).trans hη⟩

/-- **Covering a compact set by Euclidean balls, keeping a chain off the closed balls.**

If `A ⊆ e.source` is compact and `c` is a `k`-chain supported away from `A`, then `A` is covered by
finitely many `e`-preimages of Euclidean open balls whose closed balls lie in `e.target` and whose
preimages are disjoint from the support of `c`; in particular `c` is still supported off the union
of the closed balls. -/
theorem exists_suppS_compl_iUnion_balls {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {A : Set M} (hA : IsCompact A) (hAe : A ⊆ e.source) (k : ℕ)
    (c : Work.Compact.Noncompact.Ch (TopCat.of M) k)
    (hc : c ∈ Work.Compact.Noncompact.suppS (TopCat.of M) (Aᶜ) k) :
    ∃ (m : ℕ) (y : Fin m → EuclideanSpace ℝ (Fin n)) (r : Fin m → ℝ),
      (∀ i, 0 < r i) ∧ (∀ i, Metric.closedBall (y i) (r i) ⊆ e.target) ∧
      A ⊆ ⋃ i, (e.source ∩ e ⁻¹' Metric.ball (y i) (r i)) ∧
      c ∈ Work.Compact.Noncompact.suppS (TopCat.of M)
        ((⋃ i, (e.source ∩ e ⁻¹' Metric.closedBall (y i) (r i)))ᶜ) k := by
  classical
  -- Expand `c` as a finite combination of generators whose simplices avoid `A`.
  obtain ⟨T, a, hcT, hsupp⟩ := (mem_suppS_iff_of_expansion k c (Aᶜ)).mp hc
  -- `K` is the support of `c`: a compact set disjoint from `A`.
  let T' : Finset (SimplexT (TopCat.of M) k) := T.filter (fun σ => a σ ≠ 0)
  let K : Set M := ⋃ σ ∈ T', SimplexSet σ
  have hKcomp : IsCompact K := T'.isCompact_biUnion (fun σ _ => isCompact_SimplexSet σ)
  have hKsub : K ⊆ Aᶜ := by
    intro z hz
    obtain ⟨σ, hzσ⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hσT, hzσ⟩ := Set.mem_iUnion.mp hzσ
    exact hsupp σ (Finset.mem_of_mem_filter σ hσT) (Finset.mem_filter.mp hσT).2 hzσ
  -- For every `a ∈ A` pick a radius whose closed ball stays off `K` and inside `e.target`.
  have hkey : ∀ x : A, ∃ ε : ℝ, 0 < ε ∧
      Metric.closedBall (e x.1) ε ⊆ e.target ∧
      (e.source ∩ e ⁻¹' Metric.closedBall (e x.1) ε) ⊆ Kᶜ := by
    intro x
    have hxsrc : x.1 ∈ e.source := hAe x.2
    have hxK : x.1 ∈ Kᶜ := fun hx => hKsub hx x.2
    obtain ⟨ε₁, hε₁pos, hε₁sub⟩ :=
      exists_closedBall_subset_of_open e hxsrc hKcomp.isClosed.isOpen_compl hxK
    obtain ⟨δ, hδpos, hδsub⟩ := exists_closedBall_subset_target e hxsrc
    refine ⟨min ε₁ δ, lt_min hε₁pos hδpos, ?_, ?_⟩
    · exact (Metric.closedBall_subset_closedBall (min_le_right _ _)).trans hδsub
    · exact (Set.inter_subset_inter_right _
        (Set.preimage_mono (Metric.closedBall_subset_closedBall (min_le_left _ _)))).trans hε₁sub
  choose ε hεpos hεtarget hεK using hkey
  -- The corresponding open balls cover `A`; extract a finite subcover.
  let U : A → Set M := fun x => e.source ∩ e ⁻¹' Metric.ball (e x.1) (ε x)
  have hUopen : ∀ x : A, IsOpen (U x) := fun x => e.isOpen_inter_preimage Metric.isOpen_ball
  have hcover : A ⊆ ⋃ x, U x := by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hAe hz, Metric.mem_ball_self (hεpos ⟨z, hz⟩)⟩
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover U hUopen hcover
  refine ⟨t.card, fun i => e ((t.equivFin.symm i).1.1), fun i => ε ((t.equivFin.symm i).1),
    ?_, ?_, ?_, ?_⟩
  · intro i; exact hεpos _
  · intro i; exact hεtarget _
  · intro z hz
    obtain ⟨x, hzU⟩ := Set.mem_iUnion.mp (ht hz)
    obtain ⟨hxt, hzU⟩ := Set.mem_iUnion.mp hzU
    refine Set.mem_iUnion.mpr ⟨t.equivFin ⟨x, hxt⟩, ?_⟩
    have hsym : t.equivFin.symm (t.equivFin ⟨x, hxt⟩) = ⟨x, hxt⟩ := Equiv.symm_apply_apply _ _
    simp only [hsym]
    exact hzU
  · -- `c` is supported off the union of the closed balls, since that union avoids `K`.
    refine (mem_suppS_iff_of_expansion k c _).mpr ⟨T, a, hcT, ?_⟩
    intro σ hσT haσ
    have hσ' : σ ∈ T' := Finset.mem_filter.mpr ⟨hσT, haσ⟩
    have hsubK : SimplexSet σ ⊆ K := by
      intro z hz
      exact Set.mem_iUnion.mpr ⟨σ, Set.mem_iUnion.mpr ⟨hσ', hz⟩⟩
    have hKsubS : K ⊆ (⋃ i, (e.source ∩
        e ⁻¹' Metric.closedBall (e ((t.equivFin.symm i).1.1)) (ε ((t.equivFin.symm i).1))))ᶜ := by
      intro z hzK hzS
      obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hzS
      exact hεK (t.equivFin.symm i) hzi hzK
    exact Set.Subset.trans hsubK hKsubS

end

end Work.Compact.Noncompact

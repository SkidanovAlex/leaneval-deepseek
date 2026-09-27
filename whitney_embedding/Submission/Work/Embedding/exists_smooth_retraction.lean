import Mathlib
import Submission.Work.Embedding.exists_unique_closest_point
import Submission.Work.Embedding.chartRepN_adjoint_min
import Submission.Work.Embedding.orthogonal_range_mfderiv
import Submission.Work.Embedding.local_retraction_model

open scoped Manifold ContDiff
open Topology Metric Filter Set

namespace Work.Embedding

/-- **Tubular neighbourhood theorem** (smooth retraction form).  A compact smooth submanifold of
`ℝ^N` admits a smooth nearest-point retraction on a neighbourhood of it, and the displacement of a
point of that neighbourhood is orthogonal to the tangent space of the submanifold. -/
theorem exists_smooth_retraction {n N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [Nonempty M]
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 n) (𝓡 N) ∞ e)
    (hinj : Function.Injective e)
    (himm : ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 N) e x)) :
    ∃ (U : Set (EuclideanSpace ℝ (Fin N)))
      (π : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)),
      IsOpen U ∧ Set.range e ⊆ U ∧ ContDiffOn ℝ ∞ π U ∧
      (∀ x, π (e x) = e x) ∧
      (∀ y ∈ U, π y ∈ Set.range e ∧ dist y (π y) = infDist y (Set.range e)) ∧
      (∀ y ∈ U, ∃ x : M, π y = e x ∧ y - e x ∈ (mfderiv (𝓡 n) (𝓡 N) e x).rangeᗮ) := by
  obtain ⟨ε, hεpos, huniq⟩ := exists_unique_closest_point e he hinj himm
  let np : EuclideanSpace ℝ (Fin N) → M := fun y =>
    if h : infDist y (Set.range e) < ε then Classical.choose (huniq y h)
    else Classical.arbitrary M
  have hnp_dist : ∀ y (h : infDist y (Set.range e) < ε),
      dist y (e (np y)) = infDist y (Set.range e) := by
    intro y h
    have hnp : np y = Classical.choose (huniq y h) := by
      simp only [np]
      exact dif_pos h
    rw [hnp]
    exact (Classical.choose_spec (huniq y h)).1
  have hloc : ∀ p : M, ∃ O g, IsOpen O ∧ e p ∈ O ∧ (∀ y ∈ O, infDist y (Set.range e) < ε) ∧
      ContDiffOn ℝ ∞ g O ∧
      (∀ y ∈ O, ∀ q : M, dist y (e q) = infDist y (Set.range e) → e q = g y) :=
    fun p => local_retraction_model e he hinj himm hεpos huniq p
  let Oset : M → Set (EuclideanSpace ℝ (Fin N)) := fun p => Classical.choose (hloc p)
  let gset : M → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) :=
    fun p => Classical.choose (Classical.choose_spec (hloc p))
  have hOset : ∀ p, IsOpen (Oset p) ∧ e p ∈ Oset p ∧
      (∀ y ∈ Oset p, infDist y (Set.range e) < ε) ∧ ContDiffOn ℝ ∞ (gset p) (Oset p) ∧
      (∀ y ∈ Oset p, ∀ q : M, dist y (e q) = infDist y (Set.range e) → e q = gset p y) := by
    intro p
    exact Classical.choose_spec (Classical.choose_spec (hloc p))
  have hπ_eq : ∀ p y, y ∈ Oset p → e (np y) = gset p y := by
    intro p y hy
    have htube := (hOset p).2.2.1 y hy
    exact (hOset p).2.2.2.2 y hy (np y) (hnp_dist y htube)
  refine ⟨⋃ p, Oset p, (fun y => e (np y)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isOpen_iUnion fun p => (hOset p).1
  · intro x hx
    obtain ⟨x', rfl⟩ := hx
    exact mem_iUnion.mpr ⟨x', (hOset x').2.1⟩
  · refine contDiffOn_of_locally_contDiffOn fun y hy => ?_
    obtain ⟨p, hp⟩ := mem_iUnion.mp hy
    refine ⟨Oset p, (hOset p).1, hp, ?_⟩
    exact (((hOset p).2.2.2.1).mono Set.inter_subset_right).congr
      (fun z hz => hπ_eq p z hz.2)
  · intro x
    have h0 : infDist (e x) (Set.range e) = 0 := by
      refine le_antisymm ?_ Metric.infDist_nonneg
      calc infDist (e x) (Set.range e) ≤ dist (e x) (e x) :=
            Metric.infDist_le_dist_of_mem (Set.mem_range_self x)
        _ = 0 := dist_self _
    have hlt : infDist (e x) (Set.range e) < ε := by rw [h0]; exact hεpos
    have hxp : np (e x) = x := by
      have hcl : dist (e x) (e x) = infDist (e x) (Set.range e) := by rw [dist_self, h0]
      have huniq' := (Classical.choose_spec (huniq (e x) hlt)).2 x hcl
      have h3 : np (e x) = Classical.choose (huniq (e x) hlt) := by
        simp only [np]
        exact dif_pos hlt
      rw [h3, ← huniq']
    show e (np (e x)) = e x
    rw [hxp]
  · intro y hy
    obtain ⟨p, hp⟩ := mem_iUnion.mp hy
    have htube := (hOset p).2.2.1 y hp
    exact ⟨Set.mem_range_self (np y), hnp_dist y htube⟩
  · intro y hy
    obtain ⟨p, hp⟩ := mem_iUnion.mp hy
    have htube := (hOset p).2.2.1 y hp
    refine ⟨np y, rfl, ?_⟩
    have hmin : ∀ z : M, dist y (e (np y)) ≤ dist y (e z) := by
      intro z
      rw [hnp_dist y htube]
      exact Metric.infDist_le_dist_of_mem (Set.mem_range_self z)
    have hstat := chartRepN_adjoint_min e he
      (mem_chart_source (EuclideanSpace ℝ (Fin n)) (np y)) hmin
    exact (orthogonal_range_mfderiv e he
      (mem_chart_source (EuclideanSpace ℝ (Fin n)) (np y)) (y - e (np y))).mpr hstat

end Work.Embedding

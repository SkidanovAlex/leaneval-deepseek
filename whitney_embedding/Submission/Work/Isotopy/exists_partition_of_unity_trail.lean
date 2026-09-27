import Mathlib

namespace Work.Isotopy

open scoped Manifold ContDiff
open Topology Set Function

/-- **A smooth partition of unity supported on a family of boxes and summing to one on the trail.**
Given finitely many open sets `O_j ⊆ ℝ`, `B_j ⊆ ℝ^N` covering the "trail"
`{(s, Φ s x) | s ∈ [a,b], x : M}` of a continuous family `Φ` over a compact manifold `M`, there are
smooth nonnegative functions `ψ_j` on `ℝ × ℝ^N`, supported in `O_j × B_j`, whose sum is `1` at every
point of the trail. -/
theorem exists_partition_of_unity_trail {n N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M]
    {ι : Type} [Fintype ι] {O : ι → Set ℝ} {B : ι → Set (EuclideanSpace ℝ (Fin N))}
    (hO : ∀ j, IsOpen (O j)) (hB : ∀ j, IsOpen (B j))
    {Φ : ℝ → M → EuclideanSpace ℝ (Fin N)} (hc : Continuous (Function.uncurry Φ)) (a b : ℝ)
    (hcover : ∀ s ∈ Set.Icc a b, ∀ x, ∃ j, s ∈ O j ∧ Φ s x ∈ B j) :
    ∃ ψ : ι → ℝ → EuclideanSpace ℝ (Fin N) → ℝ,
      (∀ j, ContDiff ℝ ∞ (Function.uncurry (ψ j))) ∧
      (∀ j s z, 0 ≤ ψ j s z) ∧
      (∀ j s z, ψ j s z ≠ 0 → s ∈ O j ∧ z ∈ B j) ∧
      (∀ s ∈ Set.Icc a b, ∀ x, ∑ j, ψ j s (Φ s x) = 1) := by
  classical
  -- The trail of `Φ` over the parameter interval `[a,b]`: a compact subset of `ℝ × ℝ^N`.
  set T : Set (ℝ × EuclideanSpace ℝ (Fin N)) :=
    {p | ∃ s ∈ Set.Icc a b, ∃ x : M, p = (s, Φ s x)} with hT
  have hT_eq : T
      = (fun p : ℝ × M => (p.1, Φ p.1 p.2)) '' (Set.Icc a b ×ˢ (Set.univ : Set M)) := by
    rw [hT]
    ext p
    constructor
    · rintro ⟨s, hs, x, rfl⟩
      exact ⟨(s, x), ⟨hs, trivial⟩, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.1, hq.1, q.2, rfl⟩
  -- The trail is compact, hence closed, being the continuous image of `[a,b] × M`.
  have hTclosed : IsClosed T := by
    rw [hT_eq]
    exact ((isCompact_Icc.prod isCompact_univ).image (continuous_fst.prodMk hc)).isClosed
  -- The boxes `O j ×ˢ B j` cover the trail.
  have hcover' : T ⊆ ⋃ j, O j ×ˢ B j := by
    intro p hp
    rw [hT] at hp
    obtain ⟨s, hs, x, rfl⟩ := hp
    obtain ⟨j, hj1, hj2⟩ := hcover s hs x
    exact mem_iUnion_of_mem j ⟨hj1, hj2⟩
  -- A smooth partition of unity on the trail, subordinate to the boxes.
  obtain ⟨ρ, hρsub⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin N)))
      hTclosed (fun j => O j ×ˢ B j) (fun j => (hO j).prod (hB j)) hcover'
  refine ⟨fun j s z => ρ j (s, z), ?_, ?_, ?_, ?_⟩
  · intro j
    exact (ρ j).contMDiff.contDiff
  · intro j s z
    exact ρ.nonneg j (s, z)
  · intro j s z hz
    have hmem : (s, z) ∈ tsupport (ρ j) :=
      subset_tsupport _ (by simpa using hz)
    have hbox := hρsub j hmem
    simpa using hbox
  · intro s hs x
    have hp : (s, Φ s x) ∈ T := by
      rw [hT]
      exact ⟨s, hs, x, rfl⟩
    have h1 := ρ.sum_eq_one hp
    rwa [finsum_eq_sum_of_fintype] at h1

end Work.Isotopy

import Mathlib

/-!
# A smooth partition of unity on the trail of an arc family

Given finitely many boxes `O j × B j` covering the trail `{(s, Φ s x) : s ∈ [a,b], x ∈ [0,1]}` of a
continuous family `Φ : ℝ → ℝ → ℝ^m` over the compact set `[a,b] × [0,1]`, there are smooth
nonnegative functions `ψ j` on `ℝ × ℝ^m`, supported in `O j × B j`, whose sum is `1` at every point
of the trail.

This is the arc version of `Work.Isotopy.exists_partition_of_unity_trail` (compact manifold source);
the trail here is the image of the compact `[a,b] × [0,1]`, and the partition of unity is the one
Mathlib produces for that closed set.
-/

open scoped Manifold ContDiff
open Topology Set MeasureTheory

namespace Work.Whitney.CutPush

/-- **A smooth partition of unity on the trail of an arc family.** -/
theorem partition_of_unity_trail_arc {m : ℕ} {ι : Type} [Fintype ι]
    {O : ι → Set ℝ} {B : ι → Set (EuclideanSpace ℝ (Fin m))}
    (hO : ∀ j, IsOpen (O j)) (hB : ∀ j, IsOpen (B j))
    {Φ : ℝ → ℝ → EuclideanSpace ℝ (Fin m)} (hc : Continuous (Function.uncurry Φ)) (a b : ℝ)
    (hcover : ∀ s ∈ Set.Icc a b, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ j, s ∈ O j ∧ Φ s x ∈ B j) :
    ∃ ψ : ι → ℝ → EuclideanSpace ℝ (Fin m) → ℝ,
      (∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (ψ j))) ∧
      (∀ j s z, 0 ≤ ψ j s z) ∧
      (∀ j, tsupport (fun p : ℝ × EuclideanSpace ℝ (Fin m) => ψ j p.1 p.2) ⊆ O j ×ˢ B j) ∧
      (∀ s ∈ Set.Icc a b, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∑ j, ψ j s (Φ s x) = 1) := by
  classical
  set T : Set (ℝ × EuclideanSpace ℝ (Fin m)) :=
    {p | ∃ s ∈ Set.Icc a b, ∃ x ∈ Set.Icc (0 : ℝ) 1, p = (s, Φ s x)} with hT
  have hT_eq : T = (fun p : ℝ × ℝ => (p.1, Φ p.1 p.2)) '' (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1) := by
    rw [hT]
    ext p
    constructor
    · rintro ⟨s, hs, x, hx, rfl⟩
      exact ⟨(s, x), ⟨hs, hx⟩, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.1, hq.1, q.2, hq.2, rfl⟩
  have hTclosed : IsClosed T := by
    rw [hT_eq]
    exact ((isCompact_Icc.prod isCompact_Icc).image (continuous_fst.prodMk hc)).isClosed
  have hcover' : T ⊆ ⋃ j, O j ×ˢ B j := by
    intro p hp
    rw [hT] at hp
    obtain ⟨s, hs, x, hx, rfl⟩ := hp
    obtain ⟨j, hj1, hj2⟩ := hcover s hs x hx
    exact Set.mem_iUnion_of_mem j ⟨hj1, hj2⟩
  obtain ⟨ρ, hρsub⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin m)))
      hTclosed (fun j => O j ×ˢ B j) (fun j => (hO j).prod (hB j)) hcover'
  refine ⟨fun j s z => ρ j (s, z), ?_, ?_, ?_, ?_⟩
  · intro j
    exact (ρ j).contMDiff.contDiff
  · intro j s z
    exact ρ.nonneg j (s, z)
  · intro j
    simpa using hρsub j
  · intro s hs x hx
    have hp : (s, Φ s x) ∈ T := ⟨s, hs, x, hx, rfl⟩
    have h1 := ρ.sum_eq_one hp
    rwa [finsum_eq_sum_of_fintype] at h1

end Work.Whitney.CutPush

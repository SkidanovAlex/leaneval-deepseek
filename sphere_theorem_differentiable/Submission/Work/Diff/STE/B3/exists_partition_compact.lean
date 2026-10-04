import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

theorem exists_partition_compact {n : ℕ} {ι : Type*} [Fintype ι]
    (K : Set (Fin n → ℝ)) (hK : IsCompact K)
    (U : ι → Set (Fin n → ℝ)) (hU : ∀ i, IsOpen (U i)) (hcov : K ⊆ ⋃ i, U i) :
    ∃ ψ : ι → (Fin n → ℝ) → ℝ,
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i)) ∧
      (∀ i (z : Fin n → ℝ), 0 ≤ ψ i z) ∧
      (∀ i, tsupport (ψ i) ⊆ U i) ∧
      (∀ i, HasCompactSupport (ψ i)) ∧
      (∀ z ∈ K, ∑ i, ψ i z = 1) := by
  classical
  -- A closed ball containing `K`, so that all supports we produce are bounded.
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : Fin n → ℝ)
  -- Shrink the cover to `U i ∩ ball 0 r`; the resulting functions have support in a fixed ball.
  set V : ι → Set (Fin n → ℝ) := fun i => U i ∩ Metric.ball 0 r with hV
  have hVopen : ∀ i, IsOpen (V i) := fun i => (hU i).inter Metric.isOpen_ball
  have hVcov : K ⊆ ⋃ i, V i := by
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hz)
    exact Set.mem_iUnion.mpr ⟨i, hi, hr hz⟩
  -- Mathlib's smooth partition of unity subordinate to the open cover `V` of the closed set `K`.
  obtain ⟨θ, hθ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Fin n → ℝ)) hK.isClosed V hVopen hVcov
  refine ⟨fun i => (θ i : (Fin n → ℝ) → ℝ), ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    intro i
    exact contMDiff_iff_contDiff.mp (θ i).contMDiff
  · -- nonnegativity
    intro i z
    exact θ.nonneg i z
  · -- subordination: `tsupport (θ i) ⊆ V i ⊆ U i`
    intro i
    exact Set.Subset.trans (hθ i) Set.inter_subset_left
  · -- compact support: `tsupport (θ i) ⊆ ball 0 r ⊆ closedBall 0 r`
    intro i
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Fin n → ℝ) r)
      (isClosed_tsupport _) ?_
    exact Set.Subset.trans (hθ i)
      (Set.Subset.trans Set.inter_subset_right Metric.ball_subset_closedBall)
  · -- the sum equals one on `K` (a finite sum, as `ι` is a fintype)
    intro z hz
    simpa only [finsum_eq_sum_of_fintype] using θ.sum_eq_one hz

end Work.Diff.STE.B3

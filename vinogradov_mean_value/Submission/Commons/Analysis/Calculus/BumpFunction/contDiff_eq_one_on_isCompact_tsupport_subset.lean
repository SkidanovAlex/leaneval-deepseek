import Submission.Commons.Analysis.Calculus.BumpFunction.contDiff_eq_one_on_isClosed_tsupport_subset

namespace Commons.Analysis.Calculus.BumpFunction

open Set Metric

open scoped ContDiff ENNReal in
theorem contDiff_eq_one_on_isCompact_tsupport_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) : ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧ (∀ x ∈ K, f x = 1) ∧ tsupport f ⊆ U ∧ HasCompactSupport f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 1) := by
  -- Bound `K` inside a closed ball.
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : E)
  -- Restrict `U` to a bounded open neighbourhood of `K`.
  have hU' : IsOpen (U ∩ ball (0 : E) (R + 1)) := hU.inter isOpen_ball
  have hKU' : K ⊆ U ∩ ball (0 : E) (R + 1) := by
    intro x hx
    refine ⟨hKU hx, ?_⟩
    have hx' := hR hx
    rw [mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (mem_closedBall_zero_iff.mp hx') (lt_add_one R)
  obtain ⟨f, hf_diff, hf_one, hf_ts, hf_nonneg, hf_le⟩ :=
    contDiff_eq_one_on_isClosed_tsupport_subset hK.isClosed hU' hKU'
  refine ⟨f, hf_diff, hf_one, hf_ts.trans inter_subset_left, ?_, hf_nonneg, hf_le⟩
  exact (isCompact_closedBall (0 : E) (R + 1)).of_isClosed_subset
    (isClosed_tsupport f) (hf_ts.trans (inter_subset_right.trans ball_subset_closedBall))

end Commons.Analysis.Calculus.BumpFunction

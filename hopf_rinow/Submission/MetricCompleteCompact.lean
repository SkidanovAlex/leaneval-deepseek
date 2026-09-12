import Mathlib

/-! If closed balls around every point are compact then the space is complete. -/

open scoped ENNReal
open Set Filter
open EMetric -- for `closedBall`, the extended (ℝ≥0∞-radius) closed ball
set_option linter.deprecated false

namespace Submission
namespace Metric

variable {M : Type*} [EMetricSpace M]

/-- A pseudoemetric (uniform) space in which every closed ball is compact is complete:
any Cauchy sequence lies in a compact closed ball, hence has a convergent subsequence,
and a Cauchy sequence with a convergent subsequence converges. -/
lemma complete_of_closedBalls_compact
    (h : ∀ p : M, ∀ R : ℝ≥0∞, IsCompact (closedBall p R)) : CompleteSpace M := by
  -- It suffices to prove that every Cauchy sequence converges.
  refine EMetric.complete_of_cauchySeq_tendsto ?_
  intro u hu
  -- The Cauchy sequence is eventually confined to a closed ball of radius one.
  rcases EMetric.cauchySeq_iff.mp hu (1 : ℝ≥0∞) (by norm_num) with ⟨N, hN⟩
  have hmem : ∀ᶠ n in atTop, u n ∈ closedBall (u N) (1 : ℝ≥0∞) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (Metric.mem_closedEBall).2 (le_of_lt (hN n hn N (le_rfl)))
  -- ... which is compact, so `u` has a cluster point `x` there.
  have hmap : Filter.map u atTop ≤ 𝓟 (closedBall (u N) (1 : ℝ≥0∞)) := by
    rwa [le_principal_iff, mem_map]
  rcases (h (u N) (1 : ℝ≥0∞)).exists_mapClusterPt (f := atTop) (u := u) hmap with
    ⟨x, -, hxc⟩
  -- A Cauchy sequence with a cluster point converges to it.
  exact ⟨x, le_nhds_of_cauchy_adhp hu hxc⟩

end Metric
end Submission

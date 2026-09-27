import Mathlib

namespace Work.Mostow

/-- A continuous map from `ℝⁿ` to `ℝⁿ` can be approximated uniformly on a ball by a `C¹` map.

This is a (very small) instance of the standard smoothing argument: convolve `u` with a smooth
bump function of small support.  Mathlib packages the whole construction in
`Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le`; the only work left here is to
turn uniform continuity of `u` on a slightly larger closed ball into the pointwise local
closeness hypothesis of that lemma. -/
theorem exists_contDiff_dist_le_on_closedBall (n : ℕ) (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hu : Continuous u) (ε : ℝ) (hε : 0 < ε) :
    ∃ G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      ContDiff ℝ 1 G ∧ ∀ x ∈ Metric.closedBall 0 2, dist (G x) (u x) ≤ ε := by
  have hS : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 3) :=
    isCompact_closedBall _ _
  have huc : UniformContinuousOn u (Metric.closedBall 0 3) :=
    hS.uniformContinuousOn_of_continuous hu.continuousOn
  rcases Metric.uniformContinuousOn_iff.mp huc ε hε with ⟨δ, hδpos, hδ⟩
  rcases hu.exists_contDiff_dist_le_of_forall_mem_ball_dist_le
    (lt_min hδpos (one_pos : (0 : ℝ) < 1)) with ⟨g, hgc, hg⟩
  refine ⟨g, hgc.of_le (WithTop.coe_le_coe.mpr le_top), ?_⟩
  intro x hx
  apply hg x ε
  intro y hy
  rw [Metric.mem_ball] at hy
  apply le_of_lt
  rw [dist_comm]
  refine hδ x ?_ y ?_ ?_
  · rw [Metric.mem_closedBall]; linarith [Metric.mem_closedBall.mp hx]
  · rw [Metric.mem_closedBall]
    calc dist y 0 ≤ dist y x + dist x 0 := dist_triangle y x 0
      _ ≤ 1 + 2 := by
          have h1 : dist y x < 1 := lt_of_lt_of_le hy (min_le_right δ 1)
          linarith [Metric.mem_closedBall.mp hx]
      _ = 3 := by norm_num
  · rw [dist_comm]; exact lt_of_lt_of_le hy (min_le_left δ 1)

end Work.Mostow

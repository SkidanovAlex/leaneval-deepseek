import Mathlib
import Submission.Lib.Unif2.Work.Modulus.Defs

namespace Work.Modulus

open scoped Convex

/-- **Chart balls are path connected, in a strong form.**  If `x` lies in the chart source with
`c x = a`, and `z` lies in the chart ball `chartBall c a ρ` (whose Euclidean image is contained in
the chart target), then there is a path from `x` to `z` whose image is contained in the chart ball.

The path is the straight segment from `a` to `c z` in `ℂ`, read back through the chart: it stays in
`Metric.ball a ρ` by convexity of the ball, hence in `c.target`, so that `c.symm` may be applied to
it continuously. -/
theorem exists_path_in_chartBall
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (c : OpenPartialHomeomorph Y ℂ) {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.ball a ρ ⊆ c.target)
    {x z : Y} (hx : x ∈ c.source) (hxa : c x = a)
    (hz : z ∈ Submission.chartBall c a ρ) :
    ∃ η : Path x z, ∀ t, η t ∈ Submission.chartBall c a ρ := by
  have hzsrc : z ∈ c.source := hz.1
  have hzball : c z ∈ Metric.ball a ρ := hz.2
  have haball : a ∈ Metric.ball a ρ := by simpa using hρ
  -- the straight segment from `a` to `c z` in `ℂ` stays inside the Euclidean ball
  set γ := Path.segment a (c z) with hγ
  have hγrange : ∀ t, γ t ∈ Metric.ball a ρ := by
    intro t
    have ht : γ t ∈ [a -[ℝ] c z] := by
      rw [← Path.range_segment]
      exact ⟨t, rfl⟩
    exact (convex_ball a ρ).segment_subset haball hzball ht
  -- read the segment back through the chart
  have hcont : Continuous (fun t : unitInterval => c.symm (γ t)) :=
    c.continuousOn_symm.comp_continuous γ.continuous (fun t => hsub (hγrange t))
  refine ⟨⟨⟨fun t => c.symm (γ t), hcont⟩, ?_, ?_⟩, ?_⟩
  · show c.symm (γ 0) = x
    rw [Path.source, ← hxa]
    exact c.left_inv hx
  · show c.symm (γ 1) = z
    rw [Path.target]
    exact c.left_inv hzsrc
  · intro t
    show c.symm (γ t) ∈ c.source ∧ c (c.symm (γ t)) ∈ Metric.ball a ρ
    exact ⟨c.map_target (hsub (hγrange t)),
      by rw [c.right_inv (hsub (hγrange t))]; exact hγrange t⟩

end Work.Modulus

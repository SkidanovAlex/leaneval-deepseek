import Mathlib

namespace Work.RPB.B1a

lemma exists_ball_forall_le_norm_segment_sub {a b w : ℂ} (hw : w ∉ segment ℝ a b) :
    ∃ d > 0, ∀ x ∈ Metric.ball w d, ∀ y ∈ segment ℝ a b, d ≤ ‖y - x‖ := by
  -- The segment is the continuous image of the compact interval `Icc 0 1`, hence compact.
  have hcompact : IsCompact (segment ℝ a b) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by continuity)
  have hne : (segment ℝ a b).Nonempty := ⟨a, left_mem_segment ℝ a b⟩
  -- Since the segment is closed and `w` is outside it, its distance to `w` is positive.
  have hpos : 0 < Metric.infDist w (segment ℝ a b) :=
    (hcompact.isClosed.notMem_iff_infDist_pos hne).mp hw
  refine ⟨Metric.infDist w (segment ℝ a b) / 2, by linarith, ?_⟩
  intro x hx y hy
  rw [Metric.mem_ball, dist_comm] at hx
  have h1 : Metric.infDist w (segment ℝ a b) ≤ dist w y := Metric.infDist_le_dist_of_mem hy
  have h2 : dist w y ≤ dist w x + dist x y := dist_triangle w x y
  have : dist x y = ‖y - x‖ := by rw [dist_eq_norm, norm_sub_rev]
  rw [← this]
  linarith

end Work.RPB.B1a

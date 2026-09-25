import Mathlib

namespace Work.NN.Core

open scoped ContDiff

lemma lipschitzOn_ball_of_contDiffAt_one {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiffAt ℝ 1 f 0)
    (h0 : f 0 = 0) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      (∀ x, ‖x‖ < r → ‖f x‖ ≤ C * ‖x‖) ∧
      (∀ x y, ‖x‖ < r → ‖y‖ < r → ‖f x - f y‖ ≤ C * ‖x - y‖) := by
  obtain ⟨K, t, ht, hK⟩ := hf.exists_lipschitzOnWith
  rcases Metric.mem_nhds_iff.mp ht with ⟨r, hr, hrt⟩
  refine ⟨r, (K : ℝ) + 1, hr, by positivity, ?_, ?_⟩
  · intro x hx
    have hxt : x ∈ t := hrt (by rw [Metric.mem_ball, dist_zero_right]; exact hx)
    have h0t : (0 : E) ∈ t := mem_of_mem_nhds ht
    have hb := hK.dist_le_mul x hxt 0 h0t
    rw [h0, dist_zero_right, dist_zero_right] at hb
    calc ‖f x‖ ≤ (K : ℝ) * ‖x‖ := hb
      _ ≤ ((K : ℝ) + 1) * ‖x‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  · intro x y hx hy
    have hxt : x ∈ t := hrt (by rw [Metric.mem_ball, dist_zero_right]; exact hx)
    have hyt : y ∈ t := hrt (by rw [Metric.mem_ball, dist_zero_right]; exact hy)
    have hb := hK.dist_le_mul x hxt y hyt
    rw [dist_eq_norm, dist_eq_norm] at hb
    calc ‖f x - f y‖ ≤ (K : ℝ) * ‖x - y‖ := hb
      _ ≤ ((K : ℝ) + 1) * ‖x - y‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

end Work.NN.Core

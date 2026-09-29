import Mathlib
import Submission.Work.C17.logPw_setup

/-!
# The stadium lies in the unit disc, in weak form (`Work.C17I.stadium_subset_ball_weak`)

Let `p₀ = 1/4 + i/5` and `stadiumSet c δ ρ = ⋃_{t ∈ [0,1]} ball ((1-t)c + t·p₀) ((1-t)δ + tρ)`.
If `0 ≤ c`, `c + δ ≤ 1` and `‖p₀‖ + ρ ≤ 1`, then every point of the stadium satisfies `‖z‖ < 1`.

For `z` in the slice of parameter `t` the triangle inequality gives

`‖z‖ < ((1-t)δ + tρ) + ((1-t)c + t‖p₀‖) = (1-t)(c+δ) + t(‖p₀‖+ρ) ≤ 1`,

because `c + δ ≤ 1`, `‖p₀‖ + ρ ≤ 1` and `0 ≤ t ≤ 1`.
-/

namespace Work.C17I

open Work.C17

theorem stadium_subset_ball_weak {c δ ρ : ℝ} (hc : 0 ≤ c) (h1 : c + δ ≤ 1)
    (h2 : ‖Work.C17.p0C‖ + ρ ≤ 1) :
    Work.C17.stadiumSet c δ ρ ⊆ Metric.ball (0 : ℂ) 1 := by
  -- norm of a real number seen in `ℂ`
  have normR : ∀ r : ℝ, ‖(r : ℂ)‖ = |r| := by
    intro r
    have h : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
    nlinarith [norm_nonneg (r : ℂ), abs_nonneg r, sq_abs r]
  intro z hz
  obtain ⟨t, ht, hzmem⟩ := hz
  rw [Metric.mem_ball, dist_zero_right]
  rw [Metric.mem_ball] at hzmem
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  set w : ℂ := (((1 - t) * c : ℝ) : ℂ) + (t : ℂ) * p0C with hw
  have hlt : ‖z - w‖ < (1 - t) * δ + t * ρ := by
    rw [dist_eq_norm] at hzmem; exact hzmem
  have hwbound : ‖w‖ ≤ (1 - t) * c + t * ‖p0C‖ := by
    rw [hw]
    calc ‖(((1 - t) * c : ℝ) : ℂ) + (t : ℂ) * p0C‖
        ≤ ‖(((1 - t) * c : ℝ) : ℂ)‖ + ‖(t : ℂ) * p0C‖ := norm_add_le _ _
      _ = (1 - t) * c + t * ‖p0C‖ := by
          rw [norm_mul, normR, normR]
          rw [abs_of_nonneg (mul_nonneg (by linarith) hc), abs_of_nonneg ht0]
  have hle : (1 - t) * δ + t * ρ + ((1 - t) * c + t * ‖p0C‖) ≤ 1 := by
    nlinarith [h1, h2, ht0, ht1]
  have hfin : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
    calc ‖z‖ = ‖(z - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
  linarith

end Work.C17I

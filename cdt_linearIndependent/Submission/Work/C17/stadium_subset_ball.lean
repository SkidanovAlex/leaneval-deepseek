import Mathlib
import Submission.Work.C17.logPw_setup

/-!
# The stadium is contained in the unit disc (`Work.C17.stadium_subset_ball`)

For `3/4 ≤ c < 1`, `δ = min ((1-c)/2) (1/64)` and `ρ = 1/64`, every point of the
stadium `stadiumSet c δ ρ = ⋃_{t ∈ [0,1]} ball ((1-t)c + t·p₀) ((1-t)δ + tρ)`
satisfies `‖z‖ < 1`.

Since `‖p₀‖ = √41/20 < 63/64`, and `c + δ ≤ (1+c)/2 < 1`, for `z` in the slice of
parameter `t` the triangle inequality gives

`‖z‖ < ((1-t)δ + tρ) + ((1-t)c + t‖p₀‖) = (1-t)(c+δ) + t(‖p₀‖+ρ) ≤ 1`,
-/

namespace Work.C17

theorem stadium_subset_ball {c δ ρ : ℝ} (hc : 3 / 4 ≤ c) (hc1 : c < 1)
    (hδ : δ = min ((1 - c) / 2) (1 / 64)) (hρ : ρ = 1 / 64) :
    stadiumSet c δ ρ ⊆ Metric.ball (0 : ℂ) 1 := by
  -- norm of a real number seen in `ℂ`
  have normR : ∀ r : ℝ, ‖(r : ℂ)‖ = |r| := by
    intro r
    have h : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
    nlinarith [norm_nonneg (r : ℂ), abs_nonneg r, sq_abs r]
  -- `‖p₀‖ = √41/20 < 63/64`
  have hp0 : ‖p0C‖ < 63 / 64 := by
    have h : Complex.normSq p0C = 41 / 400 := by
      unfold p0C; simp [Complex.normSq_apply]; norm_num
    have h2 : ‖p0C‖ ^ 2 = 41 / 400 := by
      rw [← Complex.normSq_eq_norm_sq]; exact h
    nlinarith [norm_nonneg p0C]
  intro z hz
  obtain ⟨t, ht, hzmem⟩ := hz
  rw [Metric.mem_ball, dist_zero_right]
  rw [Metric.mem_ball] at hzmem
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hc0 : 0 ≤ c := by linarith
  have hδle : δ ≤ (1 - c) / 2 := by rw [hδ]; exact min_le_left _ _
  have hA : c + δ ≤ 1 := by nlinarith
  have hB : ‖p0C‖ + ρ ≤ 1 := by rw [hρ]; nlinarith
  set w : ℂ := (((1 - t) * c : ℝ) : ℂ) + (t : ℂ) * p0C with hw
  have hlt : ‖z - w‖ < (1 - t) * δ + t * ρ := by
    rw [dist_eq_norm] at hzmem; exact hzmem
  have hwbound : ‖w‖ ≤ (1 - t) * c + t * ‖p0C‖ := by
    rw [hw]
    calc ‖(((1 - t) * c : ℝ) : ℂ) + (t : ℂ) * p0C‖
        ≤ ‖(((1 - t) * c : ℝ) : ℂ)‖ + ‖(t : ℂ) * p0C‖ := norm_add_le _ _
      _ = (1 - t) * c + t * ‖p0C‖ := by
          rw [norm_mul, normR, normR]
          rw [abs_of_nonneg (mul_nonneg (by linarith) hc0), abs_of_nonneg ht0]
  have hle : (1 - t) * δ + t * ρ + ((1 - t) * c + t * ‖p0C‖) ≤ 1 := by
    nlinarith [hA, hB, ht0, ht1]
  have hfin : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
    calc ‖z‖ = ‖(z - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
  linarith

end Work.C17

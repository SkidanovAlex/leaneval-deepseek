import Mathlib
import Submission.Work.Pert.Basic

namespace Work.Pert

theorem u_lipschitz_halfball_le {rr : ℝ} {u : ℂ → ℂ} {σ τ : ℂ}
    (hrr : 0 < rr) (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, ‖u z‖ ≤ 2)
    (hσ : ‖σ‖ ≤ rr / 2) (hτ : τ ∈ Metric.ball (0 : ℂ) rr) (hδ : ‖τ - σ‖ ≤ 1 / 4) :
    ‖u τ - u σ‖ ≤ 16 / rr * ‖τ - σ‖ := by
  have hσball : σ ∈ Metric.ball (0 : ℂ) rr := by
    rw [mem_ball_zero_iff]; linarith
  have huτ : ‖u τ‖ ≤ 2 := hu2 τ hτ
  have huσ : ‖u σ‖ ≤ 2 := hu2 σ hσball
  rcases lt_or_ge (‖τ - σ‖) (rr - ‖σ‖) with h | h
  · -- `τ` lies in the disk centered at `σ` of radius `rr - ‖σ‖`, on which a
    -- Schwarz-lemma distance estimate applies with the center `σ`.
    have hR1 : 0 < rr - ‖σ‖ := lt_of_le_of_lt (norm_nonneg _) h
    have hτball : τ ∈ Metric.ball σ (rr - ‖σ‖) := by
      rw [mem_ball_iff_norm]; exact h
    have hsub : Metric.ball σ (rr - ‖σ‖) ⊆ Metric.ball (0 : ℂ) rr := by
      intro w hw
      rw [mem_ball_iff_norm] at hw
      rw [mem_ball_zero_iff]
      have : ‖w‖ ≤ ‖w - σ‖ + ‖σ‖ := by
        calc ‖w‖ = ‖(w - σ) + σ‖ := by ring_nf
          _ ≤ ‖w - σ‖ + ‖σ‖ := norm_add_le _ _
      linarith
    have hd : DifferentiableOn ℂ u (Metric.ball σ (rr - ‖σ‖)) := hu.mono hsub
    have hmaps : Set.MapsTo u (Metric.ball σ (rr - ‖σ‖)) (Metric.closedBall (u σ) 4) := by
      intro w hw
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hw2 : ‖u w‖ ≤ 2 := hu2 w (hsub hw)
      calc ‖u w - u σ‖ ≤ ‖u w‖ + ‖u σ‖ := norm_sub_le _ _
        _ ≤ 2 + 2 := by linarith
        _ = 4 := by norm_num
    have hSch := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmaps hτball
    rw [dist_eq_norm, dist_eq_norm] at hSch
    have hle : (4 : ℝ) / (rr - ‖σ‖) ≤ 16 / rr := by
      rw [div_le_div_iff₀ hR1 hrr]
      nlinarith [hσ]
    calc ‖u τ - u σ‖ ≤ 4 / (rr - ‖σ‖) * ‖τ - σ‖ := hSch
      _ ≤ 16 / rr * ‖τ - σ‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg _)
  · -- Otherwise `‖τ - σ‖ ≥ rr/2`, so the desired bound is at least `8 ≥ 4 ≥ ‖u τ - u σ‖`.
    have hge : rr / 2 ≤ ‖τ - σ‖ := by linarith [h, hσ]
    have h4 : (4 : ℝ) ≤ 16 / rr * ‖τ - σ‖ := by
      have hpos : (0 : ℝ) ≤ 16 / rr := by positivity
      have := mul_le_mul_of_nonneg_left hge hpos
      have heq : 16 / rr * (rr / 2) = 8 := by field_simp; ring
      linarith [this]
    have hb : ‖u τ - u σ‖ ≤ 4 := by
      calc ‖u τ - u σ‖ ≤ ‖u τ‖ + ‖u σ‖ := norm_sub_le _ _
        _ ≤ 2 + 2 := by linarith
        _ = 4 := by norm_num
    linarith

end Work.Pert

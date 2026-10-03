import Mathlib
import Submission.Work.Interfaces.Parabolic

namespace Work.Pert.Ksub2

theorem hF_ratio_close_of_small {hF : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hhF0 : hF 0 = 1)
    (hhFd : DifferentiableOn ℂ hF (Metric.ball (0 : ℂ) ρ)) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ρ / 2 ∧ ∀ t : ℂ, ‖t‖ ≤ η →
      1 + t * hF t ≠ 0 ∧ ‖hF t / (1 + t * hF t) - 1‖ < 1 / 4 := by
  -- hF is holomorphic on a ball around 0, hence continuous there.
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball, dist_self]; exact hρ
  have hdiff : DifferentiableAt ℂ hF 0 :=
    hhFd.differentiableAt (Metric.isOpen_ball.mem_nhds h0)
  have hcont : ContinuousAt hF 0 := hdiff.continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδpos, hδ⟩ := hcont (1/8) (by norm_num)
  refine ⟨min (min (ρ/2) (1/24)) (δ/2), ?_, ?_, ?_⟩
  · exact lt_min (lt_min (by linarith) (by norm_num)) (by linarith)
  · exact le_trans (min_le_left _ _) (min_le_left _ _)
  · intro t ht
    have htδ : ‖t‖ < δ := by
      have h2 : min (min (ρ/2) (1/24)) (δ/2) ≤ δ/2 := min_le_right _ _
      have h3 : δ/2 < δ := by linarith
      linarith
    have hclose : ‖hF t - 1‖ < 1/8 := by
      have h := hδ (x := t) (show dist t (0:ℂ) < δ by simpa [dist_eq_norm] using htδ)
      simpa [dist_eq_norm, hhF0] using h
    have hu : ‖hF t‖ < 9/8 := by
      have h1 := norm_add_le (hF t - 1) (1:ℂ)
      rw [sub_add_cancel, norm_one] at h1
      linarith
    have htη : ‖t‖ ≤ 1/24 := le_trans ht (le_trans (min_le_left _ _) (min_le_right _ _))
    have htu_bound : ‖t * hF t‖ ≤ 3/64 := by
      rw [norm_mul]
      calc ‖t‖ * ‖hF t‖ ≤ (1/24) * (9/8) := by
            exact mul_le_mul htη (le_of_lt hu) (norm_nonneg _) (by norm_num)
        _ = 3/64 := by norm_num
    have hden_ne : (1 : ℂ) + t * hF t ≠ 0 := by
      intro h
      have hneg : t * hF t = -1 := eq_neg_of_add_eq_zero_right h
      have hnorm : ‖t * hF t‖ = 1 := by rw [hneg, norm_neg, norm_one]
      rw [hnorm] at htu_bound
      norm_num at htu_bound
    have hAeq : hF t / (1 + t * hF t) - 1 = (hF t - 1 - t * hF t) / (1 + t * hF t) := by
      rw [div_sub_one hden_ne]
      ring_nf
    have hnum : ‖hF t - 1 - t * hF t‖ ≤ 11/64 := by
      have h1 : ‖hF t - 1 - t * hF t‖ ≤ ‖hF t - 1‖ + ‖t * hF t‖ := by
        have := norm_sub_le (hF t - 1) (t * hF t); simpa using this
      linarith
    have hden_lb : (61/64 : ℝ) ≤ ‖1 + t * hF t‖ := by
      have := norm_sub_norm_le (1:ℂ) (-(t * hF t))
      simp only [norm_neg, norm_one, sub_neg_eq_add] at this
      linarith
    have hden_pos : 0 < ‖1 + t * hF t‖ := by linarith
    refine ⟨hden_ne, ?_⟩
    rw [hAeq, norm_div, div_eq_mul_inv]
    have hinv : ‖1 + t * hF t‖⁻¹ ≤ (61/64)⁻¹ :=
      (inv_le_inv₀ hden_pos (by norm_num)).mpr hden_lb
    have h1 : ‖hF t - 1 - t * hF t‖ * ‖1 + t * hF t‖⁻¹ ≤ (11/64) * (61/64)⁻¹ :=
      mul_le_mul hnum hinv (inv_nonneg.mpr (norm_nonneg _)) (by norm_num)
    have h2 : (11/64 : ℝ) * (61/64)⁻¹ = 11/61 := by norm_num
    have h3 : (11/61 : ℝ) < 1/4 := by norm_num
    linarith

end Work.Pert.Ksub2

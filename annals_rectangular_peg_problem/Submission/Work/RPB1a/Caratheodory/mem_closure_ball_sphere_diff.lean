import Mathlib

namespace Work.RPB1a.Caratheodory

theorem mem_closure_ball_sphere_diff {z₀ : ℂ} (hz₀ : z₀ ∈ Metric.sphere 0 1) {δ : ℝ} (hδ : 0 < δ) :
    z₀ ∈ closure ((Metric.ball z₀ δ ∩ Metric.sphere 0 1) \ {z₀}) := by
  have hz₀n : ‖z₀‖ = 1 := by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz₀
    exact hz₀
  have hz₀ne : z₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz₀n
    exact one_ne_zero hz₀n.symm
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hη : 0 < min δ ε := lt_min hδ hε
  -- choose a small positive angle
  set t : ℝ := min (min δ ε) 1 / 2 with htt
  have htpos : 0 < t := by
    rw [htt]; have := lt_min hη (zero_lt_one); linarith
  have htlt : t < min δ ε := by
    rw [htt]
    have hpos : (0:ℝ) < min (min δ ε) 1 := lt_min hη zero_lt_one
    have hle : min (min δ ε) 1 ≤ min δ ε := min_le_left _ _
    linarith
  have htnorm : ‖Complex.exp (Complex.I * (t:ℂ)) - 1‖ ≤ t := by
    have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t)
    rwa [Real.norm_eq_abs, abs_of_pos htpos] at this
  have hsin : 0 < Real.sin (t / 2) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith) ?_
    have hle : t ≤ 1 := by
      rw [htt]; have := min_le_right (min δ ε) (1:ℝ); linarith
    linarith [Real.pi_gt_three]
  have hexp_ne : Complex.exp (Complex.I * (t:ℂ)) ≠ 1 := by
    intro heq
    have h1 : ‖Complex.exp (Complex.I * (t:ℂ)) - 1‖ = 0 := by rw [heq, sub_self, norm_zero]
    rw [Complex.norm_exp_I_mul_ofReal_sub_one, norm_eq_zero] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact (by norm_num : (2:ℝ) ≠ 0) h
    · exact hsin.ne' h
  have hd : dist z₀ (z₀ * Complex.exp (Complex.I * (t:ℂ))) =
      ‖Complex.exp (Complex.I * (t:ℂ)) - 1‖ := by
    rw [dist_eq_norm,
      show z₀ - z₀ * Complex.exp (Complex.I * (t:ℂ)) =
        z₀ * (1 - Complex.exp (Complex.I * (t:ℂ))) by ring,
      norm_mul, hz₀n, one_mul, norm_sub_rev]
  refine ⟨z₀ * Complex.exp (Complex.I * (t:ℂ)), ?_, ?_⟩
  · rw [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_singleton_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, dist_comm, hd]
      exact lt_of_le_of_lt htnorm (lt_of_lt_of_le htlt (min_le_left δ ε))
    · rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_mul,
          Complex.norm_exp_I_mul_ofReal, hz₀n, mul_one]
    · intro hcon
      have h2 : Complex.exp (Complex.I * (t:ℂ)) = 1 := by
        have : z₀ * Complex.exp (Complex.I * (t:ℂ)) = z₀ * 1 := by rw [mul_one]; exact hcon
        exact mul_left_cancel₀ hz₀ne this
      exact hexp_ne h2
  · rw [hd]
    exact lt_of_le_of_lt htnorm (lt_of_lt_of_le htlt (min_le_right δ ε))

end Work.RPB1a.Caratheodory

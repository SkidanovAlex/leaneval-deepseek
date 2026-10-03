import Mathlib

namespace Work.Pert.PinLogDev

/-- For every complex `x`, `‖1 - exp x‖ ≤ ‖x‖ * exp ‖x‖`.
Obtained from `Complex.norm_exp_sub_sum_le_norm_mul_exp` with `n = 1`. -/
lemma norm_one_sub_exp_le_mul_exp (x : ℂ) :
    ‖1 - Complex.exp x‖ ≤ ‖x‖ * Real.exp ‖x‖ := by
  rw [norm_sub_rev]
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp x 1
  simpa using h

/-- Quantitative bound for the numerical defect of the parabolic germ: with
`σ = 1 - exp (2πiα)`, for `‖α‖ ≤ 2` and `‖α‖‖w‖ ≤ 2`,

  `‖σ w + (1 - exp (-2πiαw))‖ ≤ 16 π² e^{4π} ‖α‖ ‖w‖`.

Both terms are estimated by the elementary Lipschitz bound `‖1 - e^z‖ ≤ ‖z‖ e^{‖z‖}`
applied to `z = 2πiα` and `z = -2πiαw`, whose norms are `≤ 4π` under the hypotheses. -/
theorem tau_num_le {σ α w : ℂ}
    (hσ : σ = 1 - Complex.exp (2 * Real.pi * Complex.I * α))
    (hα : ‖α‖ ≤ 2) (hαw : ‖α‖ * ‖w‖ ≤ 2) :
    ‖σ * w + (1 - Complex.exp (-(2 * Real.pi * Complex.I * α * w)))‖
      ≤ 16 * Real.pi ^ 2 * Real.exp (4 * Real.pi) * ‖α‖ * ‖w‖ := by
  subst hσ
  set z : ℂ := 2 * Real.pi * Complex.I * α with hz
  have hz_norm : ‖z‖ = 2 * Real.pi * ‖α‖ := by
    rw [hz, Complex.norm_mul, Complex.norm_mul, Complex.norm_I, mul_one]
    congr 1
    simp
  have hz_le : ‖z‖ ≤ 4 * Real.pi := by
    rw [hz_norm]; nlinarith [hα, Real.pi_pos]
  have hzw_norm : ‖z * w‖ = 2 * Real.pi * ‖α‖ * ‖w‖ := by
    rw [Complex.norm_mul, hz_norm]
  have hzw_le : ‖z * w‖ ≤ 4 * Real.pi := by
    rw [hzw_norm]; nlinarith [hαw, Real.pi_pos]
  have hterm1 : ‖(1 - Complex.exp z) * w‖
      ≤ 2 * Real.pi * Real.exp (4 * Real.pi) * ‖α‖ * ‖w‖ := by
    rw [Complex.norm_mul]
    have h1 := norm_one_sub_exp_le_mul_exp z
    have h2 : Real.exp ‖z‖ ≤ Real.exp (4 * Real.pi) := Real.exp_le_exp.mpr hz_le
    calc ‖1 - Complex.exp z‖ * ‖w‖
        ≤ (‖z‖ * Real.exp ‖z‖) * ‖w‖ := by
          exact mul_le_mul_of_nonneg_right h1 (norm_nonneg w)
      _ ≤ (2 * Real.pi * ‖α‖ * Real.exp (4 * Real.pi)) * ‖w‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg w)
          calc ‖z‖ * Real.exp ‖z‖ ≤ (2 * Real.pi * ‖α‖) * Real.exp (4 * Real.pi) := by
                apply mul_le_mul (le_of_eq hz_norm) h2 (Real.exp_pos _).le
                positivity
            _ = 2 * Real.pi * ‖α‖ * Real.exp (4 * Real.pi) := by ring
      _ = 2 * Real.pi * Real.exp (4 * Real.pi) * ‖α‖ * ‖w‖ := by ring
  have hterm2 : ‖1 - Complex.exp (-(z * w))‖
      ≤ 2 * Real.pi * Real.exp (4 * Real.pi) * ‖α‖ * ‖w‖ := by
    have h1 := norm_one_sub_exp_le_mul_exp (-(z * w))
    rw [norm_neg] at h1
    have h2 : Real.exp ‖z * w‖ ≤ Real.exp (4 * Real.pi) := Real.exp_le_exp.mpr hzw_le
    calc ‖1 - Complex.exp (-(z * w))‖
        ≤ ‖z * w‖ * Real.exp ‖z * w‖ := h1
      _ ≤ (2 * Real.pi * ‖α‖ * ‖w‖) * Real.exp (4 * Real.pi) := by
          exact mul_le_mul (le_of_eq hzw_norm) h2 (Real.exp_pos _).le (by positivity)
      _ = 2 * Real.pi * Real.exp (4 * Real.pi) * ‖α‖ * ‖w‖ := by ring
  calc ‖(1 - Complex.exp z) * w + (1 - Complex.exp (-(z * w)))‖
      ≤ ‖(1 - Complex.exp z) * w‖ + ‖1 - Complex.exp (-(z * w))‖ := norm_add_le _ _
    _ ≤ 2 * Real.pi * Real.exp (4 * Real.pi) * ‖α‖ * ‖w‖
          + 2 * Real.pi * Real.exp (4 * Real.pi) * ‖α‖ * ‖w‖ := add_le_add hterm1 hterm2
    _ = 4 * Real.pi * Real.exp (4 * Real.pi) * ‖α‖ * ‖w‖ := by ring
    _ ≤ 16 * Real.pi ^ 2 * Real.exp (4 * Real.pi) * ‖α‖ * ‖w‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg w)
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg α)
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        nlinarith [Real.pi_pos, Real.pi_gt_three]

end Work.Pert.PinLogDev

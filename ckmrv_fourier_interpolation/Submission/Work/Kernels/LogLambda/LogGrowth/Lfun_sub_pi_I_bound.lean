import Mathlib
import Submission.Work.Kernels.LogLambda.LogNormalisation
import Submission.Work.Kernels.LogLambda.LogExtension
import Submission.Work.Kernels.LogLambda.LogConstruct

namespace Work.Kernels.LogLambda.LogGrowth

open Work.Kernels.LogLambda

/-! ## Elementary estimate for the exponential

On the region `im z ≥ 1` the theta functions are exponentially close to `1`, so the two
principal logarithms appearing in `Lfun = LU` stay in a fixed ball around `0`. -/

lemma norm_ofReal_eq_abs (x : ℝ) : ‖(x : ℂ)‖ = |x| := by simp

lemma exp_le_inv_eight_of_le_neg_pi {u : ℝ} (hu : u ≤ -Real.pi) : Real.exp u ≤ 1 / 8 := by
  have h3 : (8 : ℝ) ≤ Real.exp Real.pi := by
    have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ Real.pi by positivity)
    nlinarith [Real.pi_gt_three]
  calc Real.exp u ≤ Real.exp (-Real.pi) := Real.exp_le_exp.mpr hu
    _ = (Real.exp Real.pi)⁻¹ := by rw [Real.exp_neg]
    _ ≤ 1 / 8 := by
        rw [show (1 : ℝ) / 8 = (8 : ℝ)⁻¹ by norm_num]
        exact (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr h3

lemma thetaC00_sub_one_le_half {z : ℂ} (hz : 1 ≤ z.im) : ‖thetaC00 z - 1‖ ≤ 1 / 2 := by
  have hypos : 0 < z.im := by linarith
  have h := norm_jacobiTheta_sub_one_le (τ := z) (by simpa using hypos)
  have hre : Real.exp (-Real.pi * z.im) ≤ 1 / 8 :=
    exp_le_inv_eight_of_le_neg_pi (by nlinarith [Real.pi_pos, hz])
  have hden : (7 : ℝ) / 8 ≤ 1 - Real.exp (-Real.pi * z.im) := by linarith
  have hdenpos : 0 < 1 - Real.exp (-Real.pi * z.im) := by linarith
  have h2 : 2 / (1 - Real.exp (-Real.pi * z.im)) * Real.exp (-Real.pi * z.im) ≤ 1 / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hdenpos]
    nlinarith [hre, hden]
  exact le_trans h h2

lemma ratio_sub_one_le_half {z : ℂ} (hz : 1 ≤ z.im) :
    ‖jacobiTheta₂ (z / 2) z / 2 - 1‖ ≤ 1 / 2 := by
  have hypos : 0 < z.im := by linarith
  have h := ThetaLower.ratio_estimate z hypos
  have hre : Real.exp (-(2 * Real.pi * z.im)) ≤ 1 / 8 :=
    exp_le_inv_eight_of_le_neg_pi (by nlinarith [Real.pi_pos, hz])
  have hden : (7 : ℝ) / 8 ≤ 1 - Real.exp (-(2 * Real.pi * z.im)) := by linarith
  have hdenpos : 0 < 1 - Real.exp (-(2 * Real.pi * z.im)) := by linarith
  have h2 : Real.exp (-(2 * Real.pi * z.im)) / (1 - Real.exp (-(2 * Real.pi * z.im)))
      ≤ 1 / 2 := by
    rw [div_le_iff₀ hdenpos]
    nlinarith [hre, hden]
  exact le_trans h h2

lemma norm_log_thetaC00_le {z : ℂ} (hz : 1 ≤ z.im) : ‖Complex.log (thetaC00 z)‖ ≤ 3 / 4 := by
  have h := Complex.norm_log_one_add_half_le_self (z := thetaC00 z - 1)
    (thetaC00_sub_one_le_half hz)
  rw [show (1 : ℂ) + (thetaC00 z - 1) = thetaC00 z by ring] at h
  calc ‖Complex.log (thetaC00 z)‖ ≤ 3 / 2 * ‖thetaC00 z - 1‖ := h
    _ ≤ 3 / 2 * (1 / 2) := by linarith [thetaC00_sub_one_le_half hz]
    _ = 3 / 4 := by norm_num

lemma norm_log_ratio_le {z : ℂ} (hz : 1 ≤ z.im) :
    ‖Complex.log (jacobiTheta₂ (z / 2) z / 2)‖ ≤ 3 / 4 := by
  have h := Complex.norm_log_one_add_half_le_self (z := jacobiTheta₂ (z / 2) z / 2 - 1)
    (ratio_sub_one_le_half hz)
  rw [show (1 : ℂ) + (jacobiTheta₂ (z / 2) z / 2 - 1) = jacobiTheta₂ (z / 2) z / 2 by ring] at h
  calc ‖Complex.log (jacobiTheta₂ (z / 2) z / 2)‖
      ≤ 3 / 2 * ‖jacobiTheta₂ (z / 2) z / 2 - 1‖ := h
    _ ≤ 3 / 2 * (1 / 2) := by linarith [ratio_sub_one_le_half hz]
    _ = 3 / 4 := by norm_num

theorem Lfun_sub_pi_I_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z ∈ Work.Kernels.LogLambda.W → 1 ≤ z.im →
    ‖Work.Kernels.LogLambda.Lfun z - (Real.pi : ℂ) * Complex.I * z‖ ≤ C := by
  refine ⟨4 * Real.log 2 + 6, ?_, ?_⟩
  · have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  · intro z hzW hzim
    rw [Lfun_eq_LU_on_W z hzW]
    have hLU : LU z - (Real.pi : ℂ) * Complex.I * z
        = 4 * (Real.log 2 : ℂ) + 4 * Complex.log (jacobiTheta₂ (z / 2) z / 2)
          - 4 * Complex.log (thetaC00 z) := by
      rw [LU, thetaC10_div_exp]
      ring
    rw [hLU]
    have hlog2 : ‖(Real.log 2 : ℂ)‖ = Real.log 2 := by
      rw [norm_ofReal_eq_abs, abs_of_pos (Real.log_pos (by norm_num))]
    calc ‖4 * (Real.log 2 : ℂ) + 4 * Complex.log (jacobiTheta₂ (z / 2) z / 2)
            - 4 * Complex.log (thetaC00 z)‖
        ≤ ‖4 * (Real.log 2 : ℂ) + 4 * Complex.log (jacobiTheta₂ (z / 2) z / 2)‖
            + ‖4 * Complex.log (thetaC00 z)‖ := norm_sub_le _ _
      _ ≤ (‖4 * (Real.log 2 : ℂ)‖ + ‖4 * Complex.log (jacobiTheta₂ (z / 2) z / 2)‖)
            + ‖4 * Complex.log (thetaC00 z)‖ := by
          have h := norm_add_le (4 * (Real.log 2 : ℂ))
            (4 * Complex.log (jacobiTheta₂ (z / 2) z / 2))
          linarith
      _ = 4 * Real.log 2 + 4 * ‖Complex.log (jacobiTheta₂ (z / 2) z / 2)‖
            + 4 * ‖Complex.log (thetaC00 z)‖ := by
          simp only [norm_mul, Complex.norm_ofNat, hlog2]
      _ ≤ 4 * Real.log 2 + 4 * (3 / 4) + 4 * (3 / 4) := by
          have h1 := norm_log_ratio_le hzim
          have h2 := norm_log_thetaC00_le hzim
          linarith
      _ = 4 * Real.log 2 + 6 := by ring

end Work.Kernels.LogLambda.LogGrowth

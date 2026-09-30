import Mathlib
import Submission.Work.BMF.stepKern_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- At `z = 1` the step kernel reduces to a scalar multiple of the `α = 0`
`σ`-shifted truncated Perron integral `pskInt`, for which a uniform region bound
is available (no cancellation is lost: the value is `arctan(T/σ)/π`). -/
lemma stepKern_one_eq (σ T : ℝ) :
    Commons.Analysis.Complex.stepKern σ T 1
      = (1 / (2 * Real.pi)) * Commons.Analysis.Fourier.pskInt σ T 0 := by
  unfold Commons.Analysis.Complex.stepKern Commons.Analysis.Fourier.pskInt
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Commons.Analysis.Fourier.pskKern]
  simp only [Complex.log_one, mul_zero, Complex.exp_zero, Complex.ofReal_zero, zero_mul,
    Complex.ofReal_one, one_div]
  congr 1
  ring

/-- Uniform bound for the truncated Perron step kernel: for `σ, T, z > 0`,
`‖stepKern σ T z‖ ≤ 1 + (32/(2π)) z^σ`. -/
theorem stepKern_uniform_bound (σ T z : ℝ) (hσ : 0 < σ) (hT : 0 < T) (hz : 0 < z) :
    ‖Commons.Analysis.Complex.stepKern σ T z‖ ≤ 1 + (32 / (2 * Real.pi)) * z ^ σ := by
  by_cases hz1 : z = 1
  · -- The degenerate point `z = 1`: the kernel equals `(1/2π) · pskInt σ T 0`,
    -- whose norm is bounded by `π`, giving `≤ 1/2`.
    subst hz1
    rw [stepKern_one_eq σ T]
    have hpsk : ‖Commons.Analysis.Fourier.pskInt σ T 0‖ ≤ Real.pi := by
      have hb := Commons.Analysis.Fourier.perronKernelSigma_regionBound σ T 0 hσ hT.le
      simp only [Commons.Analysis.Fourier.pskInt, Commons.Analysis.Fourier.pskKern] at hb ⊢
      simpa using hb
    have hnorm : ‖(1 / (2 * Real.pi)) * Commons.Analysis.Fourier.pskInt σ T 0‖
        = (1 / (2 * Real.pi)) * ‖Commons.Analysis.Fourier.pskInt σ T 0‖ := by
      rw [norm_mul]
      congr 1
      rw [show (1 : ℂ) / (2 * (Real.pi : ℂ)) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by
            push_cast; ring]
      calc ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ = |1 / (2 * Real.pi)| := RCLike.norm_ofReal _
        _ = 1 / (2 * Real.pi) := abs_of_nonneg (by positivity)
    rw [hnorm]
    have h1 : (1 / (2 * Real.pi)) * ‖Commons.Analysis.Fourier.pskInt σ T 0‖ ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_left hpsk (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
      calc (1 / (2 * Real.pi)) * ‖Commons.Analysis.Fourier.pskInt σ T 0‖
          ≤ (1 / (2 * Real.pi)) * Real.pi := this
        _ = 1 / 2 := by field_simp
    have h2 : (1 / 2 : ℝ) ≤ 1 + (32 / (2 * Real.pi)) * 1 ^ σ := by
      rw [Real.one_rpow]
      have : (0 : ℝ) ≤ 32 / (2 * Real.pi) := by positivity
      linarith
    linarith
  · -- The generic point `z ≠ 1`: use the deviation of the kernel from the step
    -- function and the triangle inequality.
    have hdev := Commons.Analysis.Complex.perronStep_deviation_pos σ T z hσ hT hz hz1
    have hb : ‖(if 1 < z then (1 : ℂ) else 0)‖ ≤ 1 := by
      split_ifs with h <;> simp
    have hmin : min 1 (1 / (T * |Real.log z|)) ≤ 1 := min_le_left _ _
    have hstep_nonneg : 0 ≤ (32 / (2 * Real.pi)) * z ^ σ := by
      apply mul_nonneg
      · positivity
      · exact le_of_lt (Real.rpow_pos_of_pos hz σ)
    calc
      ‖Commons.Analysis.Complex.stepKern σ T z‖
          = ‖(Commons.Analysis.Complex.stepKern σ T z - (if 1 < z then (1 : ℂ) else 0))
              + (if 1 < z then (1 : ℂ) else 0)‖ := by rw [sub_add_cancel]
      _ ≤ ‖Commons.Analysis.Complex.stepKern σ T z - (if 1 < z then (1 : ℂ) else 0)‖
            + ‖(if 1 < z then (1 : ℂ) else 0)‖ := norm_add_le _ _
      _ ≤ (32 / (2 * Real.pi)) * z ^ σ * min 1 (1 / (T * |Real.log z|)) + 1 :=
            add_le_add hdev hb
      _ ≤ (32 / (2 * Real.pi)) * z ^ σ * 1 + 1 := by
            have hle := mul_le_mul_of_nonneg_left hmin hstep_nonneg
            linarith
      _ = 1 + (32 / (2 * Real.pi)) * z ^ σ := by ring

end Work.BMF

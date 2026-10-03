import Mathlib
import Submission.Work.Pert.norm_exp_sub_one_sub_id_le_sharp

namespace Work.Pert.Lattice

/-- **Quantitative bound for `1 - exp(-2πiδ)`.**

If `‖α‖ ≤ 1/64` and `‖δ‖ ≤ ‖α‖/20` then `‖1 - exp(-2πiδ)‖ ≤ ‖α‖/3`.

Writing `w = -2πiδ`, we have `‖w‖ = 2π‖δ‖ ≤ (π/10)‖α‖ ≤ (63/200)‖α‖ ≤ 1/2`, so the sharp
quadratic Taylor estimate `‖exp w - 1 - w‖ ≤ (29/48)‖w‖²` gives
`‖1 - exp w‖ ≤ ‖w‖ + (29/48)‖w‖² ≤ (63/200 + (29/48)(63/200)²/64)‖α‖ ≤ ‖α‖/3`,
the last constant being `≈ 0.31590 < 1/3 = 0.33333…`. -/
theorem norm_one_sub_exp_neg_two_pi_I_mul_le {α δ : ℂ} (hα64 : ‖α‖ ≤ 1 / 64)
    (hδ : ‖δ‖ ≤ ‖α‖ / 20) :
    ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * δ))‖ ≤ (1 / 3) * ‖α‖ := by
  have hα0 : 0 ≤ ‖α‖ := norm_nonneg α
  set w : ℂ := -(2 * Real.pi * Complex.I * δ) with hwdef
  have hw_norm : ‖w‖ = 2 * Real.pi * ‖δ‖ := by
    rw [hwdef, norm_neg, norm_mul, norm_mul, norm_mul]
    rw [Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_ofNat]
    rw [Real.norm_of_nonneg (le_of_lt Real.pi_pos)]
  have hstep : 2 * Real.pi * ‖δ‖ ≤ 2 * Real.pi * (‖α‖ / 20) :=
    mul_le_mul_of_nonneg_left hδ (by positivity)
  have hpi_le : Real.pi ≤ (63 / 20 : ℝ) := by linarith [Real.pi_lt_d2]
  have hw_le : ‖w‖ ≤ (63 / 200 : ℝ) * ‖α‖ := by
    rw [hw_norm]
    have h3 : (Real.pi / 10) * ‖α‖ ≤ (63 / 200 : ℝ) * ‖α‖ := by
      have hp : Real.pi / 10 ≤ (63 / 200 : ℝ) := by linarith
      exact mul_le_mul_of_nonneg_right hp hα0
    calc 2 * Real.pi * ‖δ‖ ≤ 2 * Real.pi * (‖α‖ / 20) := hstep
      _ = (Real.pi / 10) * ‖α‖ := by ring
      _ ≤ (63 / 200 : ℝ) * ‖α‖ := h3
  have hw_half : ‖w‖ ≤ 1 / 2 := by
    rw [hw_norm]
    have hα20 : ‖α‖ / 20 ≤ (1 / 64) / 20 := by linarith
    calc 2 * Real.pi * ‖δ‖ ≤ 2 * Real.pi * (‖α‖ / 20) := hstep
      _ ≤ 2 * Real.pi * ((1 / 64) / 20) := by
            exact mul_le_mul_of_nonneg_left hα20 (by positivity)
      _ = Real.pi / 640 := by ring
      _ ≤ 1 / 2 := by nlinarith [Real.pi_lt_d2]
  have hsharp := norm_exp_sub_one_sub_id_le_sharp (z := w) hw_half
  have hdecomp : (1 : ℂ) - Complex.exp w = -(Complex.exp w - 1 - w) - w := by ring
  have hbound : ‖1 - Complex.exp w‖ ≤ ‖w‖ + (29 / 48) * ‖w‖ ^ 2 := by
    calc ‖1 - Complex.exp w‖ = ‖-(Complex.exp w - 1 - w) - w‖ := by rw [hdecomp]
      _ ≤ ‖-(Complex.exp w - 1 - w)‖ + ‖w‖ := norm_sub_le _ _
      _ = ‖Complex.exp w - 1 - w‖ + ‖w‖ := by rw [norm_neg]
      _ ≤ (29 / 48) * ‖w‖ ^ 2 + ‖w‖ := by linarith
      _ = ‖w‖ + (29 / 48) * ‖w‖ ^ 2 := by ring
  have hmain : ‖w‖ + (29 / 48) * ‖w‖ ^ 2 ≤ (1 / 3) * ‖α‖ := by
    have h2 : ‖w‖ ^ 2 ≤ ((63 / 200 : ℝ) * ‖α‖) ^ 2 := by
      have := mul_le_mul hw_le hw_le (norm_nonneg w) (by positivity)
      simpa [sq] using this
    have hr2 : ‖α‖ ^ 2 ≤ (1 / 64) * ‖α‖ := by
      calc ‖α‖ ^ 2 = ‖α‖ * ‖α‖ := by ring
        _ ≤ ‖α‖ * (1 / 64) := mul_le_mul_of_nonneg_left hα64 hα0
        _ = (1 / 64) * ‖α‖ := by ring
    calc ‖w‖ + (29 / 48) * ‖w‖ ^ 2
        ≤ (63 / 200 : ℝ) * ‖α‖ + (29 / 48) * ((63 / 200 : ℝ) * ‖α‖) ^ 2 := by
          have := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 29 / 48)
          linarith
      _ = (63 / 200 : ℝ) * ‖α‖ + (29 / 48) * ((63 / 200 : ℝ) ^ 2 * ‖α‖ ^ 2) := by ring
      _ ≤ (63 / 200 : ℝ) * ‖α‖ + (29 / 48) * ((63 / 200 : ℝ) ^ 2 * ((1 / 64) * ‖α‖)) := by
          have hc : (0 : ℝ) ≤ (29 / 48) * ((63 / 200 : ℝ) ^ 2) := by norm_num
          have := mul_le_mul_of_nonneg_left hr2 hc
          linarith
      _ = ((63 / 200 : ℝ) + (29 / 48) * ((63 / 200 : ℝ) ^ 2) * (1 / 64)) * ‖α‖ := by ring
      _ ≤ (1 / 3) * ‖α‖ := by
          have hcoef : ((63 / 200 : ℝ) + (29 / 48) * ((63 / 200 : ℝ) ^ 2) * (1 / 64)) ≤ 1 / 3 := by
            norm_num
          exact mul_le_mul_of_nonneg_right hcoef hα0
  linarith [hbound, hmain]

end Work.Pert.Lattice

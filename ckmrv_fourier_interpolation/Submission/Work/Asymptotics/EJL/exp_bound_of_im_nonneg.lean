import Mathlib
import Submission.Work.Asymptotics.CuspDecay.norm_one_sub_expm_ge_third

namespace Work.Asymptotics.EJL

/-- **Lower bound for `1 - e^{-2πiw}` on the nearest-lattice half strip.**

For `w = x + iy` with `|x| ≤ 1/2` and `y ≥ 0` one has
`4‖w‖ ≤ ‖1 - e^{-2πiw}‖`.

Writing `E := e^{2πy}` (so `E ≥ 1`) the exact identity of
`Work.Asymptotics.CuspDecay.norm_sq_exp_identity` gives
`‖1 - e^{-2πiw}‖² = (1-E)² + 4E sin²(πx)`.
Since `E = e^{2πy} ≥ 1 + 2πy ≥ 1 + 4y` we get `(1-E)² = (E-1)² ≥ 16y²`, and since
`E ≥ 1` and `sin²(πx) ≥ 4x²` on `|x| ≤ 1/2` we get `4E sin²(πx) ≥ 16x²`.
Hence `‖1 - e^{-2πiw}‖² ≥ 16(x²+y²) = 16‖w‖²`, and taking square roots gives the claim. -/
theorem exp_bound_of_im_nonneg (w : ℂ) (hre : |w.re| ≤ 1 / 2) (him : 0 ≤ w.im) :
    4 * ‖w‖ ≤ ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖ := by
  have hsin4 : 4 * w.re^2 ≤ Real.sin (Real.pi * w.re)^2 :=
    Work.Asymptotics.CuspDecay.four_mul_sq_le_sin_sq w.re hre
  have hexp := Real.add_one_le_exp (2 * Real.pi * w.im)
  have hp : (4 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hb : 4 * w.im ≤ Real.exp (2 * Real.pi * w.im) - 1 := by nlinarith
  have hE1 : 1 ≤ Real.exp (2 * Real.pi * w.im) := by nlinarith
  have hmain : 16 * (w.re^2 + w.im^2) ≤
      ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖^2 := by
    rw [Work.Asymptotics.CuspDecay.norm_sq_exp_identity]
    have hA : 16 * w.im^2 ≤ (1 - Real.exp (2 * Real.pi * w.im))^2 := by
      have hnn : 0 ≤ 4 * w.im := by linarith
      have h := pow_le_pow_left₀ hnn hb 2
      calc 16 * w.im^2 = (4 * w.im)^2 := by ring
        _ ≤ (Real.exp (2 * Real.pi * w.im) - 1)^2 := h
        _ = (1 - Real.exp (2 * Real.pi * w.im))^2 := by ring
    have h1 : 16 * w.re^2 ≤ 4 * Real.sin (Real.pi * w.re)^2 := by linarith
    have h4 : 0 ≤ Real.sin (Real.pi * w.re)^2 := sq_nonneg _
    have h2 : 4 * Real.sin (Real.pi * w.re)^2 ≤
        4 * Real.exp (2 * Real.pi * w.im) * Real.sin (Real.pi * w.re)^2 := by
      have hstep : 1 * Real.sin (Real.pi * w.re)^2 ≤
          Real.exp (2 * Real.pi * w.im) * Real.sin (Real.pi * w.re)^2 :=
        mul_le_mul_of_nonneg_right hE1 h4
      linarith
    nlinarith [hA, h1, h2]
  have hsq : (4 * ‖w‖)^2 ≤ ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖^2 := by
    have heq : (4 * ‖w‖)^2 = 16 * (w.re^2 + w.im^2) := by
      rw [mul_pow, Complex.sq_norm, Complex.normSq_apply]; ring
    rw [heq]; exact hmain
  have h3 : (0:ℝ) ≤ 4 * ‖w‖ := by positivity
  have h5 : (0:ℝ) ≤ ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖ := norm_nonneg _
  have hh := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq h3, Real.sqrt_sq h5] at hh

end Work.Asymptotics.EJL

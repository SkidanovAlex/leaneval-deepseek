import Mathlib
import Submission.Work.ZeroDensity.TrapKDefs

namespace Work.ZeroDensity

/-- The averaged-interval kernel `trapK` decays quadratically away from `ν = 0`:
`‖trapK L W ν‖ ≤ 1/(W π² ν²)`.  This is the decay which makes the double sum over a
`δ`-separated set of frequencies summable. -/
theorem TrapKNormLe (L W ν : ℝ) (hW : 0 < W) (hν : ν ≠ 0) :
    ‖Work.ZeroDensity.trapK L W ν‖ ≤ 1 / (W * Real.pi ^ 2 * ν ^ 2) := by
  set c : ℂ := -(2 * Real.pi * Complex.I * (ν : ℂ)) with hc_def
  -- `c = -2πiν ≠ 0`
  have hc : c ≠ 0 := by
    have hne : (2 * Real.pi * ν : ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hν
    rw [hc_def]
    intro h
    have h1 : (2 * Real.pi : ℂ) * Complex.I * (ν:ℂ) = 0 := neg_eq_zero.mp h
    have h1' : (((2*Real.pi*ν : ℝ)) : ℂ) * Complex.I = 0 := by
      rw [← h1]; push_cast; ring
    have h2 : (((2*Real.pi*ν : ℝ)) : ℂ) = 0 := (mul_eq_zero.mp h1').resolve_right Complex.I_ne_zero
    have h3 : (2*Real.pi*ν : ℝ) = 0 := by exact_mod_cast h2
    exact hne h3
  -- the integrand equals `exp (c * t)`
  have hpoint : ∀ t : ℝ, -(2 * Real.pi * Complex.I * (ν:ℂ) * (t:ℂ)) = c * (t:ℂ) := by
    intro t; rw [hc_def]; ring
  -- inner integral
  have hinner : ∀ s : ℝ, (∫ t in s..(s+L), Complex.exp (-(2 * Real.pi * Complex.I * (ν:ℂ) * (t:ℂ))))
      = Complex.exp (c * (s:ℂ)) * ((Complex.exp (c * (L:ℂ)) - 1) / c) := by
    intro s
    rw [show (∫ t in s..(s+L), Complex.exp (-(2 * Real.pi * Complex.I * (ν:ℂ) * (t:ℂ))))
        = ∫ t in s..(s+L), Complex.exp (c * (t:ℂ)) by
      apply intervalIntegral.integral_congr
      intro t ht; exact congrArg Complex.exp (hpoint t)]
    rw [integral_exp_mul_complex hc]
    have hcast : c * ((s + L : ℝ) : ℂ) = c * (s:ℂ) + c * (L:ℂ) := by push_cast; ring
    rw [hcast, Complex.exp_add]
    field_simp
  have houter : (∫ s in (0:ℝ)..W, Complex.exp (c * (s:ℂ))) = (Complex.exp (c * (W:ℂ)) - 1) / c := by
    rw [integral_exp_mul_complex hc]; simp
  -- closed form of `trapK`
  have hmain : trapK L W ν = (W:ℂ)⁻¹ * (((Complex.exp (c * (L:ℂ)) - 1)/c) * ((Complex.exp (c * (W:ℂ)) - 1)/c)) := by
    rw [trapK]
    rw [show (∫ s in (0:ℝ)..W, ∫ t in s..(s+L), Complex.exp (-(2 * Real.pi * Complex.I * (ν:ℂ) * (t:ℂ))))
         = ∫ s in (0:ℝ)..W, Complex.exp (c*(s:ℂ)) * ((Complex.exp (c*(L:ℂ))-1)/c) by
      apply intervalIntegral.integral_congr
      intro s hs; exact hinner s]
    rw [intervalIntegral.integral_mul_const, houter]
    ring
  -- norm of `c`
  have hcI : c = -(((2 * Real.pi * ν : ℝ) : ℂ) * Complex.I) := by
    rw [hc_def]; push_cast; ring
  have hnorm_c : ‖c‖ = 2 * Real.pi * |ν| := by
    have key : |2 * Real.pi * ν| = 2 * Real.pi * |ν| := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos Real.pi_pos]
    rw [hcI, norm_neg, norm_mul, Complex.norm_I, mul_one]
    rw [show ‖(((2*Real.pi*ν:ℝ):ℂ))‖ = |2*Real.pi*ν| by simp]
    exact key
  have hnormexpL : ‖Complex.exp (c*(L:ℂ))‖ = 1 := by
    have hce : c * (L:ℂ) = ((-(2*Real.pi*ν*L) : ℝ) : ℂ) * Complex.I := by
      rw [hc_def]; push_cast; ring
    rw [hce, Complex.norm_exp_ofReal_mul_I]
  have hnormexpW : ‖Complex.exp (c*(W:ℂ))‖ = 1 := by
    have hce : c * (W:ℂ) = ((-(2*Real.pi*ν*W) : ℝ) : ℂ) * Complex.I := by
      rw [hc_def]; push_cast; ring
    rw [hce, Complex.norm_exp_ofReal_mul_I]
  have hexpL : ‖Complex.exp (c*(L:ℂ)) - 1‖ ≤ 2 := by
    calc ‖Complex.exp (c*(L:ℂ)) - 1‖ ≤ ‖Complex.exp (c*(L:ℂ))‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [hnormexpL, norm_one]
      _ = 2 := by norm_num
  have hexpW : ‖Complex.exp (c*(W:ℂ)) - 1‖ ≤ 2 := by
    calc ‖Complex.exp (c*(W:ℂ)) - 1‖ ≤ ‖Complex.exp (c*(W:ℂ))‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [hnormexpW, norm_one]
      _ = 2 := by norm_num
  have hdivL : ‖(Complex.exp (c*(L:ℂ)) - 1)/c‖ ≤ 2/‖c‖ := by
    rw [norm_div]; exact div_le_div_of_nonneg_right hexpL (norm_nonneg c)
  have hdivW : ‖(Complex.exp (c*(W:ℂ)) - 1)/c‖ ≤ 2/‖c‖ := by
    rw [norm_div]; exact div_le_div_of_nonneg_right hexpW (norm_nonneg c)
  have hnormW : ‖(W:ℂ)⁻¹‖ = W⁻¹ := by
    rw [norm_inv, show ‖(W:ℂ)‖ = |W| by simp, abs_of_pos hW]
  calc ‖trapK L W ν‖
      = ‖(W:ℂ)⁻¹ * (((Complex.exp (c*(L:ℂ))-1)/c) * ((Complex.exp (c*(W:ℂ))-1)/c))‖ := by rw [hmain]
    _ = ‖(W:ℂ)⁻¹‖ * ‖((Complex.exp (c*(L:ℂ))-1)/c)‖ * ‖((Complex.exp (c*(W:ℂ))-1)/c)‖ := by
        rw [norm_mul, norm_mul, ← mul_assoc]
    _ ≤ W⁻¹ * (2/‖c‖) * (2/‖c‖) := by
        rw [hnormW]; gcongr
    _ = 1 / (W * Real.pi ^ 2 * ν ^ 2) := by
        rw [hnorm_c]
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        have ha : |ν| ≠ 0 := abs_ne_zero.mpr hν
        have hW' : W ≠ 0 := ne_of_gt hW
        field_simp
        rw [sq_abs]

end Work.ZeroDensity

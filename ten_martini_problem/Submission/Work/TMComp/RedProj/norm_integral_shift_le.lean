import Mathlib

namespace Work.TMComp.RedProj

open Complex MeasureTheory

theorem norm_integral_shift_le (Φ : ℂ → ℂ) (s : ℝ) (k : ℤ) :
    ‖∫ x in (0:ℝ)..1, Φ ((x : ℂ) + (s : ℂ) * Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((x : ℂ) + (s : ℂ) * Complex.I)))‖
    ≤ (∫ x in (0:ℝ)..1, ‖Φ ((x : ℂ) + (s : ℂ) * Complex.I)‖) * Real.exp (2 * Real.pi * (k : ℝ) * s) := by
  have h1 : ‖∫ x in (0:ℝ)..1, Φ ((x : ℂ) + (s : ℂ) * Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((x : ℂ) + (s : ℂ) * Complex.I)))‖
      ≤ ∫ x in (0:ℝ)..1, ‖Φ ((x : ℂ) + (s : ℂ) * Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((x : ℂ) + (s : ℂ) * Complex.I)))‖ :=
    intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0:ℝ) ≤ 1)
  have h2 : (∫ x in (0:ℝ)..1, ‖Φ ((x : ℂ) + (s : ℂ) * Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((x : ℂ) + (s : ℂ) * Complex.I)))‖)
      = ∫ x in (0:ℝ)..1, ‖Φ ((x : ℂ) + (s : ℂ) * Complex.I)‖ * Real.exp (2 * Real.pi * (k : ℝ) * s) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hre : (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((x : ℂ) + (s : ℂ) * Complex.I))).re
        = 2 * Real.pi * (k : ℝ) * s := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.re_ofNat, Complex.im_ofNat, Complex.intCast_re, Complex.intCast_im]
      ring
    simp only [Complex.norm_exp, norm_mul, hre]
  calc
    ‖∫ x in (0:ℝ)..1, Φ ((x : ℂ) + (s : ℂ) * Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((x : ℂ) + (s : ℂ) * Complex.I)))‖
      ≤ ∫ x in (0:ℝ)..1, ‖Φ ((x : ℂ) + (s : ℂ) * Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((x : ℂ) + (s : ℂ) * Complex.I)))‖ := h1
    _ = ∫ x in (0:ℝ)..1, ‖Φ ((x : ℂ) + (s : ℂ) * Complex.I)‖ * Real.exp (2 * Real.pi * (k : ℝ) * s) := h2
    _ = (∫ x in (0:ℝ)..1, ‖Φ ((x : ℂ) + (s : ℂ) * Complex.I)‖) * Real.exp (2 * Real.pi * (k : ℝ) * s) := by
        rw [intervalIntegral.integral_mul_const]

end Work.TMComp.RedProj

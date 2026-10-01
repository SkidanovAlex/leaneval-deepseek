import Mathlib

open MeasureTheory

namespace Work.ZeroFreeTables.P9F

/-- `∫_0^X e^{-z t} cos(ζ t) dt = (e^{-zX}(ζ sin(ζX) - z cos(ζX)) + z) / (z^2 + ζ^2)`,
in the case `ζ ≠ 0` that makes the denominator nonzero.

Proved by writing the integrand as the real part of the complex exponential
`exp(((-z) + i ζ) t)`, integrating that complex exponential in closed form, and
taking real parts. -/
theorem integral_exp_neg_mul_cos (z ζ X : ℝ) (hζ : ζ ≠ 0) :
    ∫ t in (0:ℝ)..X, Real.exp (-(z * t)) * Real.cos (ζ * t)
      = (Real.exp (-(z * X)) * (ζ * Real.sin (ζ * X) - z * Real.cos (ζ * X)) + z) / (z ^ 2 + ζ ^ 2) := by
  set c : ℂ := ((-z : ℝ) : ℂ) + ((ζ : ℝ) : ℂ) * Complex.I with hcdef
  have hc : c ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    rw [hcdef] at hre him
    simp at hre him
    exact hζ him
  have hcre : c.re = -z := by rw [hcdef]; simp
  have hcim : c.im = ζ := by rw [hcdef]; simp
  have hnorm : Complex.normSq c = z ^ 2 + ζ ^ 2 := by
    rw [Complex.normSq_apply, hcre, hcim]; ring
  have hcXre : (c * (X : ℂ)).re = -(z * X) := by
    rw [hcdef, Complex.mul_re]; simp
  have hcXim : (c * (X : ℂ)).im = ζ * X := by
    rw [hcdef, Complex.mul_im]; simp
  have hint : IntervalIntegrable (fun t : ℝ => Complex.exp (c * (t : ℂ))) volume 0 X := by
    apply Continuous.intervalIntegrable; fun_prop
  have hpt : (fun t : ℝ => Real.exp (-(z * t)) * Real.cos (ζ * t))
      = (fun t : ℝ => (Complex.exp (c * (t : ℂ))).re) := by
    funext t
    rw [hcdef, Complex.exp_re]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
    ring_nf
  have hrieq : ∫ t in (0:ℝ)..X, (Complex.exp (c * (t : ℂ))).re
      = (∫ t in (0:ℝ)..X, Complex.exp (c * (t : ℂ))).re := by
    simpa using (intervalIntegral.intervalIntegral_re (μ := volume) (a := (0:ℝ)) (b := X)
      (f := fun t : ℝ => Complex.exp (c * (t : ℂ))) hint)
  rw [hpt, hrieq, integral_exp_mul_complex hc]
  rw [Complex.div_re, Complex.sub_re, Complex.sub_im]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, Complex.one_re, Complex.one_im,
    sub_zero]
  rw [Complex.exp_re, Complex.exp_im, hcXre, hcXim, hcre, hcim, hnorm]
  ring

end Work.ZeroFreeTables.P9F

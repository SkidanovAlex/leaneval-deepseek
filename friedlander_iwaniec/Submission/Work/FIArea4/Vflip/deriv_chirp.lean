import Mathlib

namespace Work.FIArea4.Vflip

/-- First derivative of the chirp `m(ξ) = exp(iα log|ξ|)` (a complex-valued function of the real
variable `ξ`). -/
theorem deriv_chirp (α : ℝ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    deriv (fun x : ℝ => Complex.exp (((α * Real.log |x| : ℝ) : ℂ) * Complex.I)) ξ =
      ((α : ℂ) * (ξ : ℂ)⁻¹) * Complex.I *
        Complex.exp (((α * Real.log |ξ| : ℝ) : ℂ) * Complex.I) := by
  -- derivative of `ξ ↦ log |ξ|` is `1/ξ` for `ξ ≠ 0`
  have hlogabs : HasDerivAt (fun x : ℝ => Real.log |x|) ξ⁻¹ ξ := by
    have h1 : HasDerivAt (fun x : ℝ => Real.log |x|) ((↑(SignType.sign ξ) : ℝ) / |ξ|) ξ :=
      (hasDerivAt_abs hξ).log (abs_ne_zero.mpr hξ)
    convert h1 using 1
    have ha : |ξ| ≠ 0 := abs_ne_zero.mpr hξ
    field_simp
    rw [mul_comm]
    exact (sign_mul_self ξ).symm
  -- chain rule: `ξ ↦ ((α log|ξ| : ℝ) : ℂ) * I` has derivative `((α/ξ : ℝ) : ℂ) * I`
  have h4 : HasDerivAt (fun x : ℝ => ((α * Real.log |x| : ℝ) : ℂ) * Complex.I)
      (↑(α * ξ⁻¹) * Complex.I) ξ :=
    ((hlogabs.const_mul α).ofReal_comp).mul_const Complex.I
  have h5 := h4.cexp
  rw [h5.deriv]
  simp only [Complex.ofReal_mul, Complex.ofReal_inv]
  ring

end Work.FIArea4.Vflip

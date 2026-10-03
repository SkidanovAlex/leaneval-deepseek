import Mathlib

namespace Work.FatouL1

/-- For `τ` with `|τ.re| < 1` and `τ ≠ 0`, the "cotangent minus its singular part"
`cot (π τ) - 1/(π τ)` equals the logarithmic derivative of the difference quotient
`dslope sin 0` at `π τ`.

Indeed both sides equal `(π τ · cos (π τ) - sin (π τ)) / (π τ · sin (π τ))`:
the difference quotient is `z ↦ sin z / z`, whose logarithmic derivative is the
classical "cot z - 1/z".  The hypotheses guarantee `π τ ≠ 0` and `sin (π τ) ≠ 0`
(the zeros of `sin` are the integer multiples of `π`, and `|Re τ| < 1` excludes
all of them except `0`, which is ruled out by `τ ≠ 0`). -/
theorem cot_sub_inv_eq_deriv_dslope (τ : ℂ) (hτ : τ ≠ 0) (hre : |τ.re| < 1) :
    Complex.cot (Real.pi * τ) - 1 / (Real.pi * τ) =
      deriv (dslope Complex.sin 0) (Real.pi * τ) / (dslope Complex.sin 0 (Real.pi * τ)) := by
  set x : ℂ := (Real.pi : ℂ) * τ with hx
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hx0 : x ≠ 0 := by rw [hx]; exact mul_ne_zero hpi hτ
  -- `sin x ≠ 0`: the zeros of `sin` are `k π`, and `|Re τ| < 1` forces `k = 0`, `τ = 0`.
  have hsin : Complex.sin x ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    have h1 : (Real.pi : ℂ) * τ = (Real.pi : ℂ) * (k : ℂ) := by
      rw [hx] at hk
      rw [hk]; ring
    have h2 : τ = (k : ℂ) := mul_left_cancel₀ hpi h1
    have h3 : |(k : ℝ)| < 1 := by
      rw [h2] at hre
      simpa using hre
    have hk1 : k < 1 := by exact_mod_cast (abs_lt.mp h3).2
    have hk2 : (-1 : ℤ) < k := by exact_mod_cast (abs_lt.mp h3).1
    have hk0 : k = 0 := by omega
    subst hk0
    simp at h2
    exact hτ h2
  -- The difference quotient at `x ≠ 0` is `sin x / x`.
  have hds : dslope Complex.sin 0 x = Complex.sin x / x := by
    rw [dslope_of_ne Complex.sin hx0, slope_def_field]
    simp
  -- Its derivative at `x` is `(x cos x - sin x)/x²`.
  have hderiv : deriv (dslope Complex.sin 0) x =
      (Complex.cos x * x - Complex.sin x * 1) / x ^ 2 := by
    have hf : HasDerivAt (fun z : ℂ => Complex.sin z / z)
        ((Complex.cos x * x - Complex.sin x * 1) / x ^ 2) x :=
      (Complex.hasDerivAt_sin x).div (hasDerivAt_id x) (by simpa using hx0)
    have hev : dslope Complex.sin 0 =ᶠ[nhds x] (fun z : ℂ => Complex.sin z / z) := by
      filter_upwards [isOpen_ne.mem_nhds hx0] with z hz
      rw [dslope_of_ne Complex.sin hz, slope_def_field]
      simp
    exact (hf.congr_of_eventuallyEq hev).deriv
  rw [Complex.cot_eq_cos_div_sin, hderiv, hds]
  field_simp

end Work.FatouL1

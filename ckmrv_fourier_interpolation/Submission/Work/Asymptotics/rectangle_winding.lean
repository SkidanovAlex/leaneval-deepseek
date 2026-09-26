import Mathlib

namespace Work.Asymptotics

open Complex MeasureTheory intervalIntegral

/-- Value of `log (-z) - log z` for `z` in the open lower half-plane. -/
private lemma log_neg_sub_log_of_im_neg (z : ℂ) (hi : z.im < 0) :
    Complex.log (-z) - Complex.log z = (Real.pi : ℂ) * Complex.I := by
  have h := Complex.arg_neg_eq_arg_add_pi_of_im_neg hi
  have hlog : Complex.log (-z) = Complex.log z + (Real.pi : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [Complex.log_re, norm_neg]
    · simp [Complex.log_im, h]
  rw [hlog]; ring

/-- Value of `log z - log (-z)` for `z` in the open upper half-plane. -/
private lemma log_sub_log_neg_of_im_pos (z : ℂ) (hi : 0 < z.im) :
    Complex.log z - Complex.log (-z) = (Real.pi : ℂ) * Complex.I := by
  have h := Complex.arg_neg_eq_arg_sub_pi_of_im_pos hi
  have hlog : Complex.log (-z) = Complex.log z - (Real.pi : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [Complex.log_re, norm_neg]
    · simp [Complex.log_im, h]
  rw [hlog]; ring

/-- Integral of `1/(z - w)` along a horizontal segment `x ↦ x + c`, where the segment lies
off the real axis. -/
private lemma integral_horizontal (w c : ℂ) (hc : (c - w).im ≠ 0) (a b : ℝ) :
    (∫ x : ℝ in a..b, (((x : ℂ) + c) - w)⁻¹)
      = Complex.log (((b : ℂ) + c) - w) - Complex.log (((a : ℂ) + c) - w) := by
  have him : ∀ x : ℝ, (((x : ℂ) + c) - w).im = (c - w).im := by
    intro x; simp [Complex.sub_im, Complex.add_im]
  have hcont : Continuous fun x : ℝ => (((x : ℂ) + c) - w)⁻¹ := by
    apply Continuous.inv₀
    · exact (Complex.continuous_ofReal.add continuous_const).sub continuous_const
    · intro x h
      exact hc (by rw [← him x, h]; simp)
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun x : ℝ => Complex.log (((x : ℂ) + c) - w)) ((((x : ℂ) + c) - w)⁻¹) x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => ((x : ℂ) + c) - w) 1 x := by
      have := (Complex.ofRealCLM.hasDerivAt (x := x)).add_const c
      simpa using this.sub_const w
    have h3 : (((x : ℂ) + c) - w) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; right
      rw [him x]; exact hc
    have h4 : HasDerivAt (fun t : ℝ => Complex.log (((t : ℂ) + c) - w))
        (1 / (((x : ℂ) + c) - w)) x := h1.clog_real h3
    simpa [one_div] using h4
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable a b)

/-- Integral of `1/(z - w)` along a vertical segment `y ↦ c + y * I` lying in the open right
half-plane. -/
private lemma integral_vertical_pos (w c : ℂ) (hc : 0 < (c - w).re) (a b : ℝ) :
    (∫ y : ℝ in a..b, ((c + (y : ℂ) * Complex.I) - w)⁻¹)
      = -Complex.I * (Complex.log ((c + (b : ℂ) * Complex.I) - w)
          - Complex.log ((c + (a : ℂ) * Complex.I) - w)) := by
  have hcont : Continuous fun y : ℝ => ((c + (y : ℂ) * Complex.I) - w)⁻¹ := by
    apply Continuous.inv₀
    · exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub
        continuous_const
    · intro y h
      have : ((c + (y : ℂ) * Complex.I) - w).re = (c - w).re := by
        simp [Complex.sub_re, Complex.add_re]
      rw [← this, h] at hc
      simp at hc
  have hderiv : ∀ y ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => -Complex.I * Complex.log ((c + (y : ℂ) * Complex.I) - w))
        (((c + (y : ℂ) * Complex.I) - w)⁻¹) y := by
    intro y hy
    have h2 : HasDerivAt (fun y : ℝ => (c + (y : ℂ) * Complex.I) - w) Complex.I y := by
      have := (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I
      simpa using (this.const_add c).sub_const w
    have h3 : ((c + (y : ℂ) * Complex.I) - w) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left
      have : ((c + (y : ℂ) * Complex.I) - w).re = (c - w).re := by
        simp [Complex.sub_re, Complex.add_re]
      rw [this]; exact hc
    have h4 : HasDerivAt (fun t : ℝ => Complex.log ((c + (t : ℂ) * Complex.I) - w))
        (Complex.I / ((c + (y : ℂ) * Complex.I) - w)) y := h2.clog_real h3
    have h5 := h4.const_mul (-Complex.I)
    have hkey : -Complex.I * (Complex.I / ((c + (y : ℂ) * Complex.I) - w))
        = ((c + (y : ℂ) * Complex.I) - w)⁻¹ := by
      have hII : -Complex.I * Complex.I = (1 : ℂ) := by simp [Complex.I_mul_I]
      rw [← mul_div_assoc, hII, one_div]
    rw [hkey] at h5
    exact h5
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable a b)]
  ring

/-- Integral of `1/(z - w)` along a vertical segment `y ↦ c + y * I` lying in the open left
half-plane (so the principal branch of `log` must be flipped). -/
private lemma integral_vertical_neg (w c : ℂ) (hc : (c - w).re < 0) (a b : ℝ) :
    (∫ y : ℝ in a..b, ((c + (y : ℂ) * Complex.I) - w)⁻¹)
      = -Complex.I * (Complex.log (-((c + (b : ℂ) * Complex.I) - w))
          - Complex.log (-((c + (a : ℂ) * Complex.I) - w))) := by
  have hcont : Continuous fun y : ℝ => ((c + (y : ℂ) * Complex.I) - w)⁻¹ := by
    apply Continuous.inv₀
    · exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub
        continuous_const
    · intro y h
      have : ((c + (y : ℂ) * Complex.I) - w).re = (c - w).re := by
        simp [Complex.sub_re, Complex.add_re]
      rw [← this, h] at hc
      simp at hc
  have hderiv : ∀ y ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => -Complex.I * Complex.log (-((c + (y : ℂ) * Complex.I) - w)))
        (((c + (y : ℂ) * Complex.I) - w)⁻¹) y := by
    intro y hy
    have h2 : HasDerivAt (fun y : ℝ => (c + (y : ℂ) * Complex.I) - w) Complex.I y := by
      have := (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I
      simpa using (this.const_add c).sub_const w
    have h2' : HasDerivAt (fun y : ℝ => -((c + (y : ℂ) * Complex.I) - w)) (-Complex.I) y :=
      h2.neg
    have h3 : (-((c + (y : ℂ) * Complex.I) - w)) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left
      have : (-((c + (y : ℂ) * Complex.I) - w)).re = -(c - w).re := by
        simp [Complex.sub_re, Complex.add_re]
      rw [this]; linarith
    have h4 : HasDerivAt (fun t : ℝ => Complex.log (-((c + (t : ℂ) * Complex.I) - w)))
        ((-Complex.I) / (-((c + (y : ℂ) * Complex.I) - w))) y := h2'.clog_real h3
    have h5 := h4.const_mul (-Complex.I)
    have hkey : -Complex.I * (-Complex.I / (-((c + (y : ℂ) * Complex.I) - w)))
        = ((c + (y : ℂ) * Complex.I) - w)⁻¹ := by
      have hII : -Complex.I * -Complex.I = (-1 : ℂ) := by simp [Complex.I_mul_I]
      rw [← mul_div_assoc, hII, neg_div, one_div, inv_neg, neg_neg]
    rw [hkey] at h5
    exact h5
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable a b)]
  ring

/-- The boundary integral of `1/(z - z₀)` over a rectangle containing `z₀` equals `2πi`. -/
theorem rectangle_winding (z₀ : ℂ) (x₁ x₂ y₁ y₂ : ℝ)
    (hx₁ : x₁ < z₀.re) (hx₂ : z₀.re < x₂) (hy₁ : y₁ < z₀.im) (hy₂ : z₀.im < y₂) :
    (∫ x : ℝ in x₁..x₂, (((x : ℂ) + (y₁ : ℂ) * Complex.I) - z₀)⁻¹)
      - (∫ x : ℝ in x₁..x₂, (((x : ℂ) + (y₂ : ℂ) * Complex.I) - z₀)⁻¹)
      + Complex.I * (∫ y : ℝ in y₁..y₂, (((x₂ : ℂ) + (y : ℂ) * Complex.I) - z₀)⁻¹)
      - Complex.I * (∫ y : ℝ in y₁..y₂, (((x₁ : ℂ) + (y : ℂ) * Complex.I) - z₀)⁻¹)
      = 2 * (Real.pi : ℂ) * Complex.I := by
  have hy₁' : (((y₁ : ℂ) * Complex.I) - z₀).im ≠ 0 := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one]
    intro h; linarith
  have hy₂' : (((y₂ : ℂ) * Complex.I) - z₀).im ≠ 0 := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one]
    intro h; linarith
  have hx₂' : 0 < (((x₂ : ℂ) - z₀).re) := by
    simp only [Complex.sub_re, Complex.ofReal_re]; linarith
  have hx₁' : (((x₁ : ℂ) - z₀).re) < 0 := by
    simp only [Complex.sub_re, Complex.ofReal_re]; linarith
  have hB := integral_horizontal z₀ ((y₁ : ℂ) * Complex.I) hy₁' x₁ x₂
  have hT := integral_horizontal z₀ ((y₂ : ℂ) * Complex.I) hy₂' x₁ x₂
  have hR := integral_vertical_pos z₀ (x₂ : ℂ) hx₂' y₁ y₂
  have hL := integral_vertical_neg z₀ (x₁ : ℂ) hx₁' y₁ y₂
  rw [hB, hT, hR, hL]
  have hI : ∀ y : ℂ, Complex.I * (-Complex.I * y) = y := by
    intro y; rw [← mul_assoc]; simp [Complex.I_mul_I]
  rw [hI (Complex.log (((x₂ : ℂ) + (y₂ : ℂ) * Complex.I) - z₀)
            - Complex.log (((x₂ : ℂ) + (y₁ : ℂ) * Complex.I) - z₀)),
      hI (Complex.log (-(((x₁ : ℂ) + (y₂ : ℂ) * Complex.I) - z₀))
            - Complex.log (-(((x₁ : ℂ) + (y₁ : ℂ) * Complex.I) - z₀)))]
  have lm1 : Complex.log (-(((x₁ : ℂ) + (y₁ : ℂ) * Complex.I) - z₀))
      - Complex.log (((x₁ : ℂ) + (y₁ : ℂ) * Complex.I) - z₀)
      = (Real.pi : ℂ) * Complex.I := by
    apply log_neg_sub_log_of_im_neg
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one]
    linarith
  have lm2 : Complex.log (((x₁ : ℂ) + (y₂ : ℂ) * Complex.I) - z₀)
      - Complex.log (-(((x₁ : ℂ) + (y₂ : ℂ) * Complex.I) - z₀))
      = (Real.pi : ℂ) * Complex.I := by
    apply log_sub_log_neg_of_im_pos
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one]
    linarith
  linear_combination lm1 + lm2

end Work.Asymptotics

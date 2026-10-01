import Mathlib

/-
Real part of the Laplace transform of the tent function `t ↦ (x₀ - t)₊` is
nonnegative on the closed right half-plane `Re z ≥ 0`.

The proof reduces the complex integral to
  `∫ t in 0..x₀, (x₀ - t) * exp (-σ t) * cos (τ t)`  with `σ = z.re ≥ 0`
and shows this real integral is `≥ 0` by two integrations by parts.  After the
first (with `sin (τ t) / τ`) and the second (with `(1 - cos (τ t)) / τ`) one
obtains
  `∫ = (1/τ²) * (exp (-σ x₀) * (1 - cos (τ x₀))
        + ∫ t in 0..x₀, (σ * exp (-σ t) * (2 + σ (x₀ - t))) * (1 - cos (τ t)))`,
whose right-hand side is manifestly nonnegative.  (For `τ = 0` the integrand is
already nonnegative pointwise.)
-/

namespace Work.LinnikAreas.OtherCharRepel

open MeasureTheory intervalIntegral

private lemma deriv_tent_mul_exp (x₀ σ : ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (x₀ - t) * Real.exp (-(σ * t)))
      (-(Real.exp (-(σ * t)) * (1 + σ * (x₀ - t)))) t := by
  have hlin : HasDerivAt (fun t : ℝ => x₀ - t) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub x₀
  have hinner : HasDerivAt (fun t : ℝ => -(σ * t)) (-σ) t := by
    have h' : HasDerivAt (fun y : ℝ => (-σ) * y) (-σ) t := by
      simpa using (hasDerivAt_id t).const_mul (-σ)
    convert h' using 1
    ext s; ring
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(σ * t))) (Real.exp (-(σ*t)) * (-σ)) t :=
    hinner.exp
  have h := hlin.mul hexp
  rw [show ((fun t : ℝ => x₀ - t) * fun t : ℝ => Real.exp (-(σ * t)))
        = (fun t : ℝ => (x₀ - t) * Real.exp (-(σ * t))) from by ext s; rfl] at h
  rw [show (-1 * Real.exp (-(σ * t)) + (x₀ - t) * (Real.exp (-(σ * t)) * -σ))
        = -(Real.exp (-(σ * t)) * (1 + σ * (x₀ - t))) from by ring] at h
  exact h

private lemma deriv_exp_mul_oneadd (x₀ σ : ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-(σ * t)) * (1 + σ * (x₀ - t)))
      (-σ * Real.exp (-(σ * t)) * (2 + σ * (x₀ - t))) t := by
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(σ * t))) (Real.exp (-(σ*t)) * (-σ)) t := by
    have hinner : HasDerivAt (fun t : ℝ => -(σ * t)) (-σ) t := by
      have h' : HasDerivAt (fun y : ℝ => (-σ) * y) (-σ) t := by
        simpa using (hasDerivAt_id t).const_mul (-σ)
      convert h' using 1
      ext s; ring
    exact hinner.exp
  have h1 : HasDerivAt (fun t : ℝ => x₀ - t) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub x₀
  have hpoly : HasDerivAt (fun t : ℝ => 1 + σ * (x₀ - t)) (σ * (-1)) t := by
    have h2 : HasDerivAt (fun t : ℝ => σ * (x₀ - t)) (σ * (-1)) t := h1.const_mul σ
    simpa using h2.const_add (1:ℝ)
  have h := hexp.mul hpoly
  rw [show ((fun t : ℝ => Real.exp (-(σ * t))) * fun t : ℝ => 1 + σ * (x₀ - t))
        = (fun t : ℝ => Real.exp (-(σ * t)) * (1 + σ * (x₀ - t))) from by ext s; rfl] at h
  rw [show (Real.exp (-(σ * t)) * -σ * (1 + σ * (x₀ - t)) + Real.exp (-(σ * t)) * (σ * -1))
        = (-σ * Real.exp (-(σ * t)) * (2 + σ * (x₀ - t))) from by ring] at h
  exact h

private lemma deriv_sin_div (τ : ℝ) (hτ : τ ≠ 0) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin (τ * t) / τ) (Real.cos (τ * t)) t := by
  have h1 : HasDerivAt (fun t : ℝ => Real.sin (τ * t)) (Real.cos (τ*t) * τ) t := by
    have hin : HasDerivAt (fun t : ℝ => τ * t) τ t := by simpa using (hasDerivAt_id t).const_mul τ
    simpa using hin.sin
  have h := h1.div_const τ
  rw [show (fun t : ℝ => Real.sin (τ*t) / τ) = (fun t : ℝ => Real.sin (τ*t)) / fun _ : ℝ => τ from by ext s; rfl] at h
  rw [show Real.cos (τ*t) * τ / τ = Real.cos (τ*t) from by field_simp] at h
  exact h

private lemma deriv_one_sub_cos_div (τ : ℝ) (hτ : τ ≠ 0) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (1 - Real.cos (τ * t)) / τ) (Real.sin (τ * t)) t := by
  have h1 : HasDerivAt (fun t : ℝ => 1 - Real.cos (τ * t)) (Real.sin (τ*t) * τ) t := by
    have h2 : HasDerivAt (fun t : ℝ => Real.cos (τ * t)) (-Real.sin (τ*t) * τ) t := by
      have hin : HasDerivAt (fun t : ℝ => τ * t) τ t := by simpa using (hasDerivAt_id t).const_mul τ
      simpa using hin.cos
    have h0 : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 t := hasDerivAt_const t 1
    have hsub := h0.sub h2
    rw [show ((fun _ : ℝ => (1:ℝ)) - fun t : ℝ => Real.cos (τ*t)) = (fun t : ℝ => 1 - Real.cos (τ*t)) from by ext s; rfl] at hsub
    rw [show (0 - -Real.sin (τ*t) * τ) = Real.sin (τ*t) * τ from by ring] at hsub
    exact hsub
  have h := h1.div_const τ
  rw [show (fun t : ℝ => (1 - Real.cos (τ*t)) / τ) = (fun t : ℝ => 1 - Real.cos (τ*t)) / fun _ : ℝ => τ from by ext s; rfl] at h
  rw [show Real.sin (τ*t) * τ / τ = Real.sin (τ*t) from by field_simp] at h
  exact h

theorem tentCosIntegralNonnegAux (x₀ σ τ : ℝ) (hx₀ : 0 ≤ x₀) (hσ : 0 ≤ σ) :
    0 ≤ ∫ t in (0:ℝ)..x₀, (x₀ - t) * Real.exp (-(σ * t)) * Real.cos (τ * t) := by
  rcases eq_or_ne τ 0 with hτ0 | hτ
  · subst τ
    have hcongr : ∫ t in (0:ℝ)..x₀, (x₀ - t) * Real.exp (-(σ * t)) * Real.cos (0 * t)
        = ∫ t in (0:ℝ)..x₀, (x₀ - t) * Real.exp (-(σ * t)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp
    rw [hcongr]
    apply intervalIntegral.integral_nonneg hx₀
    intro u hu
    exact mul_nonneg (sub_nonneg.mpr hu.2) (Real.exp_pos _).le
  · have hτsq : 0 < τ^2 := sq_pos_of_ne_zero hτ
    -- first integration by parts
    have hf_deriv : ∀ t ∈ Set.uIcc (0:ℝ) x₀, HasDerivAt (fun t : ℝ => (x₀ - t) * Real.exp (-(σ * t)))
        (-(Real.exp (-(σ * t)) * (1 + σ * (x₀ - t)))) t := fun t _ => deriv_tent_mul_exp x₀ σ t
    have hv1_deriv : ∀ t ∈ Set.uIcc (0:ℝ) x₀, HasDerivAt (fun t : ℝ => Real.sin (τ * t) / τ) (Real.cos (τ * t)) t :=
        fun t _ => deriv_sin_div τ hτ t
    have hf_int : IntervalIntegrable (fun t : ℝ => -(Real.exp (-(σ * t)) * (1 + σ * (x₀ - t)))) volume (0:ℝ) x₀ := by
      apply Continuous.intervalIntegrable; fun_prop
    have hv1_int : IntervalIntegrable (fun t : ℝ => Real.cos (τ * t)) volume (0:ℝ) x₀ := by
      apply Continuous.intervalIntegrable; fun_prop
    have h1a := intervalIntegral.integral_mul_deriv_eq_deriv_mul hf_deriv hv1_deriv hf_int hv1_int
    have h1a' : ∫ x in (0:ℝ)..x₀, (x₀ - x) * Real.exp (-(σ * x)) * Real.cos (τ * x)
        = (x₀ - x₀) * Real.exp (-(σ * x₀)) * (Real.sin (τ * x₀) / τ)
          - (x₀ - 0) * Real.exp (-(σ * 0)) * (Real.sin (τ * 0) / τ)
          - ∫ x in (0:ℝ)..x₀, (-(Real.exp (-(σ * x)) * (1 + σ * (x₀ - x)))) * (Real.sin (τ * x) / τ) := by
      simpa only [] using h1a
    -- second integration by parts
    have hg_deriv : ∀ t ∈ Set.uIcc (0:ℝ) x₀, HasDerivAt (fun t : ℝ => Real.exp (-(σ * t)) * (1 + σ * (x₀ - t)))
        (-σ * Real.exp (-(σ * t)) * (2 + σ * (x₀ - t))) t := fun t _ => deriv_exp_mul_oneadd x₀ σ t
    have hv2_deriv : ∀ t ∈ Set.uIcc (0:ℝ) x₀, HasDerivAt (fun t : ℝ => (1 - Real.cos (τ * t)) / τ) (Real.sin (τ * t)) t :=
        fun t _ => deriv_one_sub_cos_div τ hτ t
    have hg_int : IntervalIntegrable (fun t : ℝ => -σ * Real.exp (-(σ * t)) * (2 + σ * (x₀ - t))) volume (0:ℝ) x₀ := by
      apply Continuous.intervalIntegrable; fun_prop
    have hv2_int : IntervalIntegrable (fun t : ℝ => Real.sin (τ * t)) volume (0:ℝ) x₀ := by
      apply Continuous.intervalIntegrable; fun_prop
    have h2a := intervalIntegral.integral_mul_deriv_eq_deriv_mul hg_deriv hv2_deriv hg_int hv2_int
    have h2a' : ∫ x in (0:ℝ)..x₀, Real.exp (-(σ * x)) * (1 + σ * (x₀ - x)) * Real.sin (τ * x)
        = Real.exp (-(σ * x₀)) * (1 + σ * (x₀ - x₀)) * ((1 - Real.cos (τ * x₀)) / τ)
          - Real.exp (-(σ * 0)) * (1 + σ * (x₀ - 0)) * ((1 - Real.cos (τ * 0)) / τ)
          - ∫ x in (0:ℝ)..x₀, (-σ * Real.exp (-(σ * x)) * (2 + σ * (x₀ - x))) * ((1 - Real.cos (τ * x)) / τ) := by
      simpa only [] using h2a
    -- combine
    have hstep1 : ∫ x in (0:ℝ)..x₀, (x₀ - x) * Real.exp (-(σ * x)) * Real.cos (τ * x)
        = (1/τ) * ∫ x in (0:ℝ)..x₀, Real.exp (-(σ * x)) * (1 + σ * (x₀ - x)) * Real.sin (τ * x) := by
      rw [h1a']
      rw [show (x₀ - x₀) * Real.exp (-(σ * x₀)) * (Real.sin (τ * x₀) / τ) = 0 from by ring]
      rw [show (x₀ - 0) * Real.exp (-(σ * 0)) * (Real.sin (τ * 0) / τ) = 0 from by simp]
      rw [sub_zero, zero_sub]
      rw [← intervalIntegral.integral_neg]
      have hI : ∫ x in (0:ℝ)..x₀, -((-(Real.exp (-(σ * x)) * (1 + σ * (x₀ - x)))) * (Real.sin (τ * x) / τ))
          = ∫ x in (0:ℝ)..x₀, (1/τ) * (Real.exp (-(σ * x)) * (1 + σ * (x₀ - x)) * Real.sin (τ * x)) := by
        apply intervalIntegral.integral_congr; intro x hx; ring
      rw [hI, intervalIntegral.integral_const_mul]
    have hstep2 : ∫ x in (0:ℝ)..x₀, Real.exp (-(σ * x)) * (1 + σ * (x₀ - x)) * Real.sin (τ * x)
        = (1/τ) * (Real.exp (-(σ * x₀)) * (1 - Real.cos (τ * x₀))
            + ∫ x in (0:ℝ)..x₀, (σ * Real.exp (-(σ * x)) * (2 + σ * (x₀ - x))) * (1 - Real.cos (τ * x))) := by
      rw [h2a']
      rw [show Real.exp (-(σ * x₀)) * (1 + σ * (x₀ - x₀)) * ((1 - Real.cos (τ * x₀)) / τ)
            = (1/τ) * (Real.exp (-(σ * x₀)) * (1 - Real.cos (τ * x₀))) from by ring]
      rw [show Real.exp (-(σ * 0)) * (1 + σ * (x₀ - 0)) * ((1 - Real.cos (τ * 0)) / τ) = 0 from by simp]
      rw [sub_zero, sub_eq_add_neg]
      rw [← intervalIntegral.integral_neg]
      have hI : ∫ x in (0:ℝ)..x₀, -((-σ * Real.exp (-(σ * x)) * (2 + σ * (x₀ - x))) * ((1 - Real.cos (τ * x)) / τ))
          = ∫ x in (0:ℝ)..x₀, (1/τ) * ((σ * Real.exp (-(σ * x)) * (2 + σ * (x₀ - x))) * (1 - Real.cos (τ * x))) := by
        apply intervalIntegral.integral_congr; intro x hx; ring
      rw [hI, intervalIntegral.integral_const_mul]
      ring
    -- final nonnegativity
    have hbracket : 0 ≤ Real.exp (-(σ * x₀)) * (1 - Real.cos (τ * x₀))
            + ∫ x in (0:ℝ)..x₀, (σ * Real.exp (-(σ * x)) * (2 + σ * (x₀ - x))) * (1 - Real.cos (τ * x)) := by
      apply add_nonneg
      · exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (Real.cos_le_one _))
      · apply intervalIntegral.integral_nonneg hx₀
        intro u hu
        apply mul_nonneg
        · apply mul_nonneg
          · exact mul_nonneg hσ (Real.exp_pos _).le
          · have : 0 ≤ x₀ - u := sub_nonneg.mpr hu.2
            nlinarith [hσ, this]
        · exact sub_nonneg.mpr (Real.cos_le_one _)
    rw [hstep1, hstep2]
    have : (1/τ) * ((1/τ) * (Real.exp (-(σ * x₀)) * (1 - Real.cos (τ * x₀))
            + ∫ x in (0:ℝ)..x₀, (σ * Real.exp (-(σ * x)) * (2 + σ * (x₀ - x))) * (1 - Real.cos (τ * x))))
        = (1/τ^2) * (Real.exp (-(σ * x₀)) * (1 - Real.cos (τ * x₀))
            + ∫ x in (0:ℝ)..x₀, (σ * Real.exp (-(σ * x)) * (2 + σ * (x₀ - x))) * (1 - Real.cos (τ * x))) := by
      ring
    rw [this]
    exact mul_nonneg (by positivity) hbracket
/-- Real part of the Laplace transform of the tent function `t ↦ (x₀ - t)₊`
is nonnegative on the closed right half-plane `Re z ≥ 0`. -/
theorem tentLaplaceReNonneg (x₀ : ℝ) (hx₀ : 0 < x₀) (z : ℂ) (hz : 0 ≤ z.re) :
    0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((x₀ - t : ℝ) : ℂ)).re := by
  -- the integrand is continuous, hence interval integrable
  have hint : IntervalIntegrable
      (fun t : ℝ => Complex.exp (-(z * (t : ℂ))) * ((x₀ - t : ℝ) : ℂ)) volume (0:ℝ) x₀ := by
    apply Continuous.intervalIntegrable
    fun_prop
  -- push the real part inside the interval integral
  change 0 ≤ RCLike.re
    (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((x₀ - t : ℝ) : ℂ))
  rw [← intervalIntegral_re hint]
  -- compute the pointwise real part of the integrand
  have hcongr : ∫ t in (0:ℝ)..x₀,
        RCLike.re (Complex.exp (-(z * (t : ℂ))) * ((x₀ - t : ℝ) : ℂ))
      = ∫ t in (0:ℝ)..x₀, (x₀ - t) * Real.exp (-(z.re * t)) * Real.cos (z.im * t) := by
    apply intervalIntegral.integral_congr
    intro t _
    change (Complex.exp (-(z * (t : ℂ))) * ((x₀ - t : ℝ) : ℂ)).re
        = (x₀ - t) * Real.exp (-(z.re * t)) * Real.cos (z.im * t)
    rw [Complex.mul_re, Complex.exp_re]
    simp only [Complex.ofReal_im, mul_zero, sub_zero, Complex.ofReal_re]
    have h1 : (-(z * (t : ℂ))).re = -(z.re * t) := by
      simp [Complex.neg_re, Complex.mul_re]
    have h2 : (-(z * (t : ℂ))).im = -(z.im * t) := by
      simp [Complex.neg_im, Complex.mul_im]
    rw [h1, h2, Real.cos_neg]
    ring
  rw [hcongr]
  exact tentCosIntegralNonnegAux x₀ z.re z.im (le_of_lt hx₀) hz

end Work.LinnikAreas.OtherCharRepel

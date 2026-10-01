import Mathlib

namespace Work.LinnikAreas.Density4

theorem integral_mul_exp_neg_cos (z ζ T : ℝ) (hW : z ^ 2 + ζ ^ 2 ≠ 0) :
    ∫ t in (0:ℝ)..T, t * Real.exp (-(z * t)) * Real.cos (ζ * t)
      = Real.exp (-(z * T)) *
          ((-(z * T) / (z ^ 2 + ζ ^ 2) + (ζ ^ 2 - z ^ 2) / (z ^ 2 + ζ ^ 2) ^ 2)
              * Real.cos (ζ * T)
            + (ζ * T / (z ^ 2 + ζ ^ 2) + 2 * ζ * z / (z ^ 2 + ζ ^ 2) ^ 2)
              * Real.sin (ζ * T))
        - (ζ ^ 2 - z ^ 2) / (z ^ 2 + ζ ^ 2) ^ 2 := by
  set w : ℂ := ⟨-z, ζ⟩ with hw
  have hwne : w ≠ 0 := by
    intro h
    rw [hw] at h
    have hz : z = 0 := by
      have := congrArg Complex.re h
      simpa using this
    have hζ : ζ = 0 := by
      have := congrArg Complex.im h
      simpa using this
    rw [hz, hζ] at hW
    norm_num at hW
  let e : ℂ → ℂ := fun u => Complex.exp (w * u) * (u * w⁻¹ - w⁻¹ ^ 2)
  have hderiv : ∀ u : ℂ, HasDerivAt e (u * Complex.exp (w * u)) u := by
    intro u
    simp only [e]
    have h1 : HasDerivAt (fun u : ℂ => Complex.exp (w * u)) (w * Complex.exp (w*u)) u := by
      have hinner : HasDerivAt (fun u : ℂ => w * u) w u := by
        simpa using (hasDerivAt_id u).const_mul w
      exact ((Complex.hasDerivAt_exp (w*u)).scomp u hinner).congr_deriv (by ring)
    have h2 : HasDerivAt (fun u : ℂ => u * w⁻¹ - w⁻¹^2) (w⁻¹) u := by
      have := ((hasDerivAt_id u).mul_const (w⁻¹)).sub_const (w⁻¹^2)
      simpa using this
    refine (h1.mul h2).congr_deriv ?_
    field_simp
    ring
  have hF : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (e (s:ℂ)).re)
      (t * Real.exp (-(z * t)) * Real.cos (ζ * t)) t := by
    intro t
    have h := (hderiv (t:ℂ)).real_of_complex
    refine h.congr_deriv ?_
    rw [hw]
    rw [Complex.mul_re, Complex.exp_re]
    simp
    ring
  have hInt : ∫ t in (0:ℝ)..T, t * Real.exp (-(z * t)) * Real.cos (ζ * t)
      = (e (T:ℂ)).re - (e (0:ℂ)).re := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := T)
      (f := fun s : ℝ => (e (s:ℂ)).re)
      (f' := fun t : ℝ => t * Real.exp (-(z * t)) * Real.cos (ζ * t))
      (fun t _ => hF t)
      (Continuous.intervalIntegrable (by fun_prop) 0 T)
    simpa using h
  rw [hInt]
  simp only [e]
  rw [hw]
  simp only [Complex.exp_zero, mul_zero, zero_mul, one_mul, zero_sub]
  simp only [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im,
    Complex.sub_re, Complex.sub_im, Complex.neg_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, pow_two]
  field_simp
  ring_nf

end Work.LinnikAreas.Density4

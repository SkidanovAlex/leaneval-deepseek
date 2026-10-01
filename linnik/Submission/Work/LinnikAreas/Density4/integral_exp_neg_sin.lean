import Mathlib

namespace Work.LinnikAreas.Density4

theorem integral_exp_neg_sin (z ζ T : ℝ) (hW : z ^ 2 + ζ ^ 2 ≠ 0) :
    ∫ t in (0:ℝ)..T, Real.exp (-(z * t)) * Real.sin (ζ * t)
      = ((1 - Real.exp (-(z * T)) * Real.cos (T * ζ)) * ζ
          - Real.exp (-(z * T)) * Real.sin (T * ζ) * z) / (z ^ 2 + ζ ^ 2) := by
  -- Antiderivative of `exp (-(z*t)) * sin (ζ*t)`.
  let F : ℝ → ℝ := fun t =>
    (ζ - Real.exp (-(z * t)) * (z * Real.sin (ζ * t) + ζ * Real.cos (ζ * t))) / (z ^ 2 + ζ ^ 2)
  have hderiv : ∀ t : ℝ, HasDerivAt F (Real.exp (-(z * t)) * Real.sin (ζ * t)) t := by
    intro t
    have hsin : HasDerivAt (fun t : ℝ => Real.sin (ζ * t)) (Real.cos (ζ * t) * ζ) t :=
      (hasDerivAt_const_mul (x := t) ζ).sin
    have hcos : HasDerivAt (fun t : ℝ => Real.cos (ζ * t)) (-Real.sin (ζ * t) * ζ) t :=
      (hasDerivAt_const_mul (x := t) ζ).cos
    have hH : HasDerivAt (fun t : ℝ => z * Real.sin (ζ * t) + ζ * Real.cos (ζ * t))
        (z * (Real.cos (ζ * t) * ζ) + ζ * (-Real.sin (ζ * t) * ζ)) t :=
      (hsin.const_mul z).add (hcos.const_mul ζ)
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(z * t))) (Real.exp (-(z * t)) * (-z)) t := by
      have h : HasDerivAt (fun t : ℝ => (-z) * t) (-z) t := hasDerivAt_const_mul (x := t) (-z)
      have h' : HasDerivAt (fun t : ℝ => -(z * t)) (-z) t := by simpa only [neg_mul] using h
      exact h'.exp
    have hG := hexp.mul hH
    have h1 : HasDerivAt
        (fun t : ℝ => ζ - Real.exp (-(z * t)) * (z * Real.sin (ζ * t) + ζ * Real.cos (ζ * t)))
        (-(Real.exp (-(z * t)) * (-(z ^ 2 + ζ ^ 2)) * Real.sin (ζ * t))) t := by
      have hneg := hG.neg
      have h2 := hneg.const_add ζ
      refine h2.congr_deriv ?_
      ring
    exact (h1.div_const (z ^ 2 + ζ ^ 2)).congr_deriv (by rw [div_eq_iff hW]; ring)
  have hcont : IntervalIntegrable (fun t : ℝ => Real.exp (-(z * t)) * Real.sin (ζ * t))
      MeasureTheory.volume (0:ℝ) T :=
    (by fun_prop : Continuous fun t : ℝ => Real.exp (-(z * t)) * Real.sin (ζ * t)).intervalIntegrable 0 T
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := T)
      (f := F) (f' := fun t : ℝ => Real.exp (-(z * t)) * Real.sin (ζ * t))
      (fun t _ => hderiv t) hcont
  rw [key]
  dsimp only [F]
  rw [show T * ζ = ζ * T from mul_comm T ζ]
  simp only [mul_zero, neg_zero, Real.exp_zero, Real.sin_zero, Real.cos_zero, mul_one, one_mul,
    zero_add, sub_self, zero_div, sub_zero]
  field_simp
  ring

end Work.LinnikAreas.Density4

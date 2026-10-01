import Mathlib

namespace Work.LinnikAreas.Density4

/-- `∫₀^T e^{-zt} cos(ζt) dt = ((1 - e^{-zT} cos(Tζ)) z + e^{-zT} sin(Tζ) ζ) / (z² + ζ²)`.

An antiderivative of `e^{-zt} cos(ζt)` is `e^{-zt} (-z cos(ζt) + ζ sin(ζt)) / (z² + ζ²)`,
and the fundamental theorem of calculus gives the displayed value (evaluating at `t = 0`
contributes `-z/(z²+ζ²)`). -/
theorem integral_exp_neg_cos (z ζ T : ℝ) (hW : z ^ 2 + ζ ^ 2 ≠ 0) :
    ∫ t in (0:ℝ)..T, Real.exp (-(z * t)) * Real.cos (ζ * t)
      = ((1 - Real.exp (-(z * T)) * Real.cos (T * ζ)) * z
          + Real.exp (-(z * T)) * Real.sin (T * ζ) * ζ) / (z ^ 2 + ζ ^ 2) := by
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := T)
    (f := fun t : ℝ =>
      Real.exp (-(z*t)) * ((-z)*Real.cos (ζ*t) + ζ*Real.sin (ζ*t)) / (z^2+ζ^2))
    (f' := fun t : ℝ => Real.exp (-(z*t)) * Real.cos (ζ*t))
    (fun x _hx => by
      have hlin2 : HasDerivAt (fun t : ℝ => ζ * t) ζ x := by
        simpa using (hasDerivAt_id x).const_mul ζ
      have hlin1 : HasDerivAt (fun t : ℝ => -(z*t)) (-z) x := by
        have h := (hasDerivAt_id x).const_mul (-z)
        simpa using h
      have he : HasDerivAt (fun t => Real.exp (-(z*t))) (Real.exp (-(z*x)) * (-z)) x :=
        hlin1.exp
      have hcos : HasDerivAt (fun t => Real.cos (ζ*t)) (-Real.sin (ζ*x) * ζ) x := hlin2.cos
      have hsin : HasDerivAt (fun t => Real.sin (ζ*t)) (Real.cos (ζ*x) * ζ) x := hlin2.sin
      have hH : HasDerivAt (fun t => (-z)*Real.cos (ζ*t) + ζ*Real.sin (ζ*t))
          ((-z) * (-Real.sin (ζ*x) * ζ) + ζ * (Real.cos (ζ*x) * ζ)) x :=
        (hcos.const_mul (-z)).add (hsin.const_mul ζ)
      have hF := (he.mul hH).div_const (z^2+ζ^2)
      refine hF.congr_deriv ?_
      rw [div_eq_iff hW]
      ring)
    (by apply Continuous.intervalIntegrable; fun_prop)
  rw [key]
  simp only [mul_zero, neg_zero, Real.exp_zero, Real.cos_zero, Real.sin_zero, mul_one,
    add_zero]
  rw [mul_comm ζ T]
  field_simp
  ring

end Work.LinnikAreas.Density4

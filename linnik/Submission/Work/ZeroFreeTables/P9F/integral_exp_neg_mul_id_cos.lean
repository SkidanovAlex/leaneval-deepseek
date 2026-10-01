import Mathlib

namespace Work.ZeroFreeTables.P9F

/-- Primitive of `t ↦ e^{-zt} · t · cos(ζt)`:
`F t = e^{-zt} · ( t(ζ sin(ζt) - z cos(ζt))/(z²+ζ²)
                 + ((ζ²-z²) cos(ζt) + 2zζ sin(ζt))/(z²+ζ²)² )`. -/
theorem exp_neg_mul_id_cos_antideriv (z ζ x : ℝ) (hζ : ζ ≠ 0) :
    HasDerivAt
      (fun t : ℝ => Real.exp (-(z * t)) *
        (t * (ζ * Real.sin (ζ * t) - z * Real.cos (ζ * t)) / (z ^ 2 + ζ ^ 2)
         + ((ζ ^ 2 - z ^ 2) * Real.cos (ζ * t) + 2 * z * ζ * Real.sin (ζ * t))
            / (z ^ 2 + ζ ^ 2) ^ 2))
      (Real.exp (-(z * x)) * (x * Real.cos (ζ * x))) x := by
  have hDne : z ^ 2 + ζ ^ 2 ≠ 0 := by
    have h1 : (0:ℝ) < ζ ^ 2 := sq_pos_of_ne_zero hζ
    have h2 : (0:ℝ) ≤ z ^ 2 := sq_nonneg z
    positivity
  have hlinz : HasDerivAt (fun s : ℝ => -(z * s)) (-z) x := by
    convert! ((hasDerivAt_id x).const_mul z).neg using 1 <;> ring
  have hlinζ : HasDerivAt (fun s : ℝ => ζ * s) ζ x := by
    convert! (hasDerivAt_id x).const_mul ζ using 1 <;> ring
  have he : HasDerivAt (fun s : ℝ => Real.exp (-(z * s))) (Real.exp (-(z * x)) * (-z)) x := by
    simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_exp (-(z * x))).comp x hlinz
  have hsin : HasDerivAt (fun s : ℝ => Real.sin (ζ * s)) (Real.cos (ζ * x) * ζ) x := by
    simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_sin (ζ * x)).comp x hlinζ
  have hcos : HasDerivAt (fun s : ℝ => Real.cos (ζ * s)) (-Real.sin (ζ * x) * ζ) x := by
    simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_cos (ζ * x)).comp x hlinζ
  have hW : HasDerivAt (fun s : ℝ => ζ * Real.sin (ζ * s) - z * Real.cos (ζ * s))
      (ζ * (Real.cos (ζ * x) * ζ) - z * (-Real.sin (ζ * x) * ζ)) x :=
    (hsin.const_mul ζ).sub (hcos.const_mul z)
  have hP : HasDerivAt (fun s : ℝ => s * (ζ * Real.sin (ζ * s) - z * Real.cos (ζ * s)))
      (1 * (ζ * Real.sin (ζ * x) - z * Real.cos (ζ * x))
        + x * (ζ * (Real.cos (ζ * x) * ζ) - z * (-Real.sin (ζ * x) * ζ))) x :=
    (hasDerivAt_id x).mul hW
  have hQ : HasDerivAt
      (fun s : ℝ => (ζ ^ 2 - z ^ 2) * Real.cos (ζ * s) + 2 * z * ζ * Real.sin (ζ * s))
      ((ζ ^ 2 - z ^ 2) * (-Real.sin (ζ * x) * ζ) + 2 * z * ζ * (Real.cos (ζ * x) * ζ)) x :=
    (hcos.const_mul (ζ ^ 2 - z ^ 2)).add (hsin.const_mul (2 * z * ζ))
  have hg : HasDerivAt
      (fun s : ℝ => s * (ζ * Real.sin (ζ * s) - z * Real.cos (ζ * s)) / (z ^ 2 + ζ ^ 2)
        + ((ζ ^ 2 - z ^ 2) * Real.cos (ζ * s) + 2 * z * ζ * Real.sin (ζ * s))
            / (z ^ 2 + ζ ^ 2) ^ 2)
      ((1 * (ζ * Real.sin (ζ * x) - z * Real.cos (ζ * x))
        + x * (ζ * (Real.cos (ζ * x) * ζ) - z * (-Real.sin (ζ * x) * ζ))) / (z ^ 2 + ζ ^ 2)
       + ((ζ ^ 2 - z ^ 2) * (-Real.sin (ζ * x) * ζ) + 2 * z * ζ * (Real.cos (ζ * x) * ζ))
            / (z ^ 2 + ζ ^ 2) ^ 2) x :=
    (hP.div_const (z ^ 2 + ζ ^ 2)).add (hQ.div_const ((z ^ 2 + ζ ^ 2) ^ 2))
  have hF := he.mul hg
  convert! hF using 1
  all_goals
    try field_simp [hDne]
    try ring

theorem integral_exp_neg_mul_id_cos (z ζ X : ℝ) (hζ : ζ ≠ 0) :
    ∫ t in (0:ℝ)..X, Real.exp (-(z * t)) * (t * Real.cos (ζ * t))
      = Real.exp (-(z * X)) * (X * (ζ * Real.sin (ζ * X) - z * Real.cos (ζ * X)) / (z ^ 2 + ζ ^ 2)
          + ((ζ ^ 2 - z ^ 2) * Real.cos (ζ * X) + 2 * z * ζ * Real.sin (ζ * X)) / (z ^ 2 + ζ ^ 2) ^ 2)
        - (ζ ^ 2 - z ^ 2) / (z ^ 2 + ζ ^ 2) ^ 2 := by
  have hDne : z ^ 2 + ζ ^ 2 ≠ 0 := by
    have h1 : (0:ℝ) < ζ ^ 2 := sq_pos_of_ne_zero hζ
    have h2 : (0:ℝ) ≤ z ^ 2 := sq_nonneg z
    positivity
  let F : ℝ → ℝ := fun t =>
    Real.exp (-(z * t)) *
      (t * (ζ * Real.sin (ζ * t) - z * Real.cos (ζ * t)) / (z ^ 2 + ζ ^ 2)
       + ((ζ ^ 2 - z ^ 2) * Real.cos (ζ * t) + 2 * z * ζ * Real.sin (ζ * t))
          / (z ^ 2 + ζ ^ 2) ^ 2)
  have hderiv : ∀ t : ℝ, HasDerivAt F (Real.exp (-(z * t)) * (t * Real.cos (ζ * t))) t := by
    intro t
    simpa only [F] using exp_neg_mul_id_cos_antideriv z ζ t hζ
  have hint : IntervalIntegrable (fun t : ℝ => Real.exp (-(z * t)) * (t * Real.cos (ζ * t)))
      MeasureTheory.volume (0 : ℝ) X :=
    (by fun_prop : Continuous fun t : ℝ => Real.exp (-(z * t)) * (t * Real.cos (ζ * t)))
      |>.intervalIntegrable _ _
  have hF0 : F 0 = (ζ ^ 2 - z ^ 2) / (z ^ 2 + ζ ^ 2) ^ 2 := by
    simp only [F, Real.exp_zero, Real.sin_zero, Real.cos_zero, mul_one, mul_zero, zero_mul,
      neg_zero]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F)
      (f' := fun t => Real.exp (-(z * t)) * (t * Real.cos (ζ * t))) (fun t _ => hderiv t) hint,
    hF0]

end Work.ZeroFreeTables.P9F

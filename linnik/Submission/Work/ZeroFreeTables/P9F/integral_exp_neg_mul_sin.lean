import Mathlib

namespace Work.ZeroFreeTables.P9F

/-- Antiderivative of `t ↦ e^{-zt} sin(ζt)`: `F t = -e^{-zt}(z sin(ζt) + ζ cos(ζt)) / (z²+ζ²)`,
used as the primitive in `integral_exp_neg_mul_sin`. -/
theorem exp_neg_mul_sin_antideriv (z ζ x : ℝ) (hζ : ζ ≠ 0) :
    HasDerivAt
      (fun t : ℝ => -(Real.exp (-(z * t)) * (z * Real.sin (ζ * t) + ζ * Real.cos (ζ * t)))
        / (z ^ 2 + ζ ^ 2))
      (Real.exp (-(z * x)) * Real.sin (ζ * x)) x := by
  have hDne : z ^ 2 + ζ ^ 2 ≠ 0 := by
    have h1 : (0:ℝ) < ζ ^ 2 := sq_pos_of_ne_zero hζ
    have h2 : (0:ℝ) ≤ z ^ 2 := sq_nonneg z
    positivity
  have hlinz : HasDerivAt (fun s : ℝ => -(z * s)) (-z) x := by
    convert! ((hasDerivAt_id x).const_mul z).neg using 1; ring
  have hlinζ : HasDerivAt (fun s : ℝ => ζ * s) ζ x := by
    convert! (hasDerivAt_id x).const_mul ζ using 1; ring
  have he : HasDerivAt (fun s : ℝ => Real.exp (-(z * s))) (Real.exp (-(z * x)) * (-z)) x := by
    simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_exp (-(z * x))).comp x hlinz
  have hsin : HasDerivAt (fun s : ℝ => Real.sin (ζ * s)) (Real.cos (ζ * x) * ζ) x := by
    simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_sin (ζ * x)).comp x hlinζ
  have hcos : HasDerivAt (fun s : ℝ => Real.cos (ζ * s)) (-Real.sin (ζ * x) * ζ) x := by
    simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_cos (ζ * x)).comp x hlinζ
  have hsum : HasDerivAt (fun s : ℝ => z * Real.sin (ζ * s) + ζ * Real.cos (ζ * s))
      (z * (Real.cos (ζ * x) * ζ) + ζ * (-Real.sin (ζ * x) * ζ)) x :=
    (hsin.const_mul z).add (hcos.const_mul ζ)
  have hG : HasDerivAt
      (fun s : ℝ => Real.exp (-(z * s)) * (z * Real.sin (ζ * s) + ζ * Real.cos (ζ * s)))
      (-(z ^ 2 + ζ ^ 2) * Real.exp (-(z * x)) * Real.sin (ζ * x)) x := by
    have h := he.mul hsum
    convert! h using 1; ring
  have hF0 := (hG.neg).div_const (z ^ 2 + ζ ^ 2)
  convert! hF0 using 1
  all_goals
    try field_simp [hDne]
    try ring

theorem integral_exp_neg_mul_sin (z ζ X : ℝ) (hζ : ζ ≠ 0) :
    ∫ t in (0:ℝ)..X, Real.exp (-(z * t)) * Real.sin (ζ * t)
      = (ζ - Real.exp (-(z * X)) * (z * Real.sin (ζ * X) + ζ * Real.cos (ζ * X))) / (z ^ 2 + ζ ^ 2) := by
  have hDne : z ^ 2 + ζ ^ 2 ≠ 0 := by
    have h1 : (0:ℝ) < ζ ^ 2 := sq_pos_of_ne_zero hζ
    have h2 : (0:ℝ) ≤ z ^ 2 := sq_nonneg z
    positivity
  let F : ℝ → ℝ := fun t =>
    -(Real.exp (-(z * t)) * (z * Real.sin (ζ * t) + ζ * Real.cos (ζ * t))) / (z ^ 2 + ζ ^ 2)
  have hderiv : ∀ t : ℝ, HasDerivAt F (Real.exp (-(z * t)) * Real.sin (ζ * t)) t := by
    intro t
    have h := exp_neg_mul_sin_antideriv z ζ t hζ
    simpa only [F] using h
  have hint : IntervalIntegrable (fun t : ℝ => Real.exp (-(z * t)) * Real.sin (ζ * t))
      MeasureTheory.volume (0 : ℝ) X :=
    (by fun_prop : Continuous fun t : ℝ => Real.exp (-(z * t)) * Real.sin (ζ * t)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F)
      (f' := fun t => Real.exp (-(z * t)) * Real.sin (ζ * t)) (fun t _ => hderiv t) hint]
  dsimp only [F]
  simp only [mul_zero, neg_zero, Real.exp_zero, Real.sin_zero, Real.cos_zero, mul_one,
    one_mul, zero_add]
  field_simp [hDne]
  ring

end Work.ZeroFreeTables.P9F

import Mathlib

namespace Work.LinnikAreas.DhRepel

/-- An explicit antiderivative for `t ↦ exp (a * t) * (L - t)`: the function
`t ↦ exp (a * t) * (L / a + 1 / a ^ 2 - t / a)` has derivative `exp (a * t) * (L - t)`. -/
private theorem hasDerivAt_exp_mul_sub_antideriv (a L t : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.exp (a * t) * (L / a + 1 / a ^ 2 - t / a))
      (Real.exp (a * t) * (L - t)) t := by
  have h1 : HasDerivAt (fun t : ℝ => a * t) a t := by
    simpa using (hasDerivAt_id t).const_mul a
  have h2 : HasDerivAt (fun t : ℝ => Real.exp (a * t)) (Real.exp (a * t) * a) t := h1.exp
  have hid : HasDerivAt (fun t : ℝ => t / a) (1 / a) t := (hasDerivAt_id t).div_const a
  have h3 : HasDerivAt (fun t : ℝ => L / a + 1 / a ^ 2 - t / a) (-(1 / a)) t :=
    hid.const_sub (L / a + 1 / a ^ 2)
  have h4 := h2.mul h3
  refine h4.congr_deriv ?_
  field_simp
  ring

theorem integral_exp_mul_sub (a L : ℝ) (ha : a ≠ 0) (hL : 0 ≤ L) :
    ∫ t in (0:ℝ)..L, Real.exp (a * t) * (L - t) = (Real.exp (a * L) - a * L - 1) / a ^ 2 := by
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) L,
      HasDerivAt (fun t : ℝ => Real.exp (a * t) * (L / a + 1 / a ^ 2 - t / a))
        (Real.exp (a * t) * (L - t)) t :=
    fun t _ => hasDerivAt_exp_mul_sub_antideriv a L t ha
  have hint : IntervalIntegrable (fun t : ℝ => Real.exp (a * t) * (L - t)) MeasureTheory.volume 0 L :=
    (by fun_prop : Continuous fun t : ℝ => Real.exp (a * t) * (L - t)).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h]
  simp only [Real.exp_zero, mul_zero]
  field_simp
  ring

end Work.LinnikAreas.DhRepel

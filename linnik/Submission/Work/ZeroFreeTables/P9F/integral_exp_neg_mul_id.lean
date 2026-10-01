import Mathlib

namespace Work.ZeroFreeTables.P9F

theorem integral_exp_neg_mul_id (z X : ℝ) (hz : z ≠ 0) :
    ∫ t in (0:ℝ)..X, Real.exp (-(z * t)) * t = (1 - Real.exp (-(z * X)) * (1 + z * X)) / z ^ 2 := by
  -- The antiderivative of `t ↦ exp (-(z*t)) * t` is `s ↦ (1 - exp (-(z*s)) * (1 + z*s)) / z^2`.
  have hderiv : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => (1 - Real.exp (-(z * s)) * (1 + z * s)) / z ^ 2)
      (Real.exp (-(z * t)) * t) t := by
    intro t
    have hlin : HasDerivAt (fun s : ℝ => z * s) z t := hasDerivAt_const_mul (x := t) z
    have hlin2 : HasDerivAt (fun s : ℝ => -(z * s)) (-z) t := hlin.neg
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(z * s))) (Real.exp (-(z * t)) * (-z)) t := by
      have hh := (Real.hasDerivAt_exp (-(z * t))).comp t hlin2
      refine hh.congr_of_eventuallyEq ?_
      filter_upwards with s
      rfl
    have hone : HasDerivAt (fun s : ℝ => 1 + z * s) z t := hlin.const_add 1
    have hprod : HasDerivAt (fun s : ℝ => Real.exp (-(z * s)) * (1 + z * s))
        (Real.exp (-(z * t)) * (-z) * (1 + z * t) + Real.exp (-(z * t)) * z) t := by
      have hh := hexp.mul hone
      refine hh.congr_of_eventuallyEq ?_
      filter_upwards with s
      rfl
    have hsub : HasDerivAt (fun s : ℝ => 1 - Real.exp (-(z * s)) * (1 + z * s))
        (-(Real.exp (-(z * t)) * (-z) * (1 + z * t) + Real.exp (-(z * t)) * z)) t := by
      have hh := hprod.const_sub 1
      refine hh.congr_of_eventuallyEq ?_
      filter_upwards with s
      rfl
    have hdiv := hsub.div_const (z ^ 2)
    refine hdiv.congr_deriv ?_
    rw [div_eq_iff (pow_ne_zero 2 hz)]
    ring
  have hint : IntervalIntegrable (fun t : ℝ => Real.exp (-(z * t)) * t) MeasureTheory.volume (0:ℝ) X := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := X)
    (f := fun s : ℝ => (1 - Real.exp (-(z * s)) * (1 + z * s)) / z ^ 2)
    (f' := fun t : ℝ => Real.exp (-(z * t)) * t)
    (fun x _ => hderiv x) hint
  rw [hftc]
  have h0 : (1 - Real.exp (-(z * 0)) * (1 + z * 0)) / z ^ 2 = 0 := by simp
  rw [h0, sub_zero]

end Work.ZeroFreeTables.P9F

import Mathlib

namespace Work.ZeroFreeTables

/-- Integration by parts against the exponential `exp (-(z * t))`, with a vanishing
right endpoint: for `g` differentiable on `[[0, b]]` with derivative `g'` and `g b = 0`,
\[
  \int_0^b e^{-zt}\, g(t)\, dt = \frac{g(0)}{z} + \frac1z \int_0^b e^{-zt}\, g'(t)\, dt .
\] -/
theorem exp_neg_mul_ibp (z : ℂ) (hz : z ≠ 0) {b : ℝ} (g g' : ℝ → ℂ)
    (hg : ∀ t ∈ Set.uIcc (0:ℝ) b, HasDerivAt g (g' t) t)
    (hgcont : ContinuousOn g (Set.uIcc 0 b))
    (hg'cont : ContinuousOn g' (Set.uIcc 0 b))
    (hb : g b = 0) :
    ∫ t in (0:ℝ)..b, Complex.exp (-(z * (t:ℂ))) * g t
      = g 0 / z + z⁻¹ * ∫ t in (0:ℝ)..b, Complex.exp (-(z * (t:ℂ))) * g' t := by
  -- The antiderivative `v t = -(z⁻¹) exp (-(z t))` of `v' t = exp (-(z t))`.
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) b,
      HasDerivAt (fun t : ℝ => -(z⁻¹) * Complex.exp (-(z * (t:ℂ))))
        (Complex.exp (-(z * (x:ℂ)))) x := by
    intro x _
    have a : HasDerivAt (fun y : ℂ => y * (-z)) (-z) (x:ℂ) := hasDerivAt_mul_const (-z)
    have b2 : HasDerivAt (Complex.exp ∘ fun y : ℂ => y * (-z))
        (Complex.exp ((x:ℂ) * (-z)) * (-z)) (x:ℂ) :=
      HasDerivAt.comp (x:ℂ) (Complex.hasDerivAt_exp ((x:ℂ) * (-z))) a
    have c : HasDerivAt (fun y : ℂ => (-(z⁻¹)) * Complex.exp (y * (-z)))
        ((-(z⁻¹)) * (Complex.exp ((x:ℂ) * (-z)) * (-z))) (x:ℂ) := b2.const_mul (-(z⁻¹))
    have d := c.comp_ofReal
    have hfun : (fun y : ℝ => (-(z⁻¹)) * Complex.exp (↑y * (-z)))
        = fun t : ℝ => -(z⁻¹) * Complex.exp (-(z * (t:ℂ))) := by
      funext t; congr 1; ring_nf
    rw [hfun] at d
    refine d.congr_deriv ?_
    have hz' : z⁻¹ * z = 1 := inv_mul_cancel₀ hz
    have harg : (x:ℂ) * (-z) = -(z * (x:ℂ)) := by ring
    rw [harg]
    calc (-(z⁻¹)) * (Complex.exp (-(z * (x:ℂ))) * (-z))
        = z⁻¹ * (Complex.exp (-(z * (x:ℂ))) * z) := by ring
      _ = (z⁻¹ * z) * Complex.exp (-(z * (x:ℂ))) := by ring
      _ = Complex.exp (-(z * (x:ℂ))) := by rw [hz']; ring
  have hg'int : IntervalIntegrable g' MeasureTheory.volume (0:ℝ) b :=
    hg'cont.intervalIntegrable
  have hv'int : IntervalIntegrable (fun t : ℝ => Complex.exp (-(z * (t:ℂ))))
      MeasureTheory.volume (0:ℝ) b := by
    apply ContinuousOn.intervalIntegrable
    fun_prop
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul hg hderiv hg'int hv'int
  -- Rewrite the left-hand integrand into the order appearing in the statement.
  have hL : (∫ x in (0:ℝ)..b, g x * Complex.exp (-(z * (x:ℂ))))
      = ∫ t in (0:ℝ)..b, Complex.exp (-(z * (t:ℂ))) * g t := by
    apply intervalIntegral.integral_congr
    intro x _
    ring
  -- Pull the constant factor `-(z⁻¹)` out of the remaining integral.
  have hsub : (∫ x in (0:ℝ)..b, g' x * (-(z⁻¹) * Complex.exp (-(z * (x:ℂ)))))
      = -(z⁻¹) * ∫ x in (0:ℝ)..b, Complex.exp (-(z * (x:ℂ))) * g' x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  have hvb : g b * (-(z⁻¹) * Complex.exp (-(z * (b:ℂ)))) = 0 := by rw [hb, zero_mul]
  have hv0 : g 0 * (-(z⁻¹) * Complex.exp (-(z * ((0:ℝ):ℂ)))) = g 0 * (-(z⁻¹)) := by
    simp
  rw [hL, hvb, hv0, hsub] at hIBP
  rw [hIBP]
  ring

end Work.ZeroFreeTables

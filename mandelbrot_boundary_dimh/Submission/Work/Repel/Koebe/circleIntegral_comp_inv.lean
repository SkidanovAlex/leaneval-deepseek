import Mathlib

namespace Work.Repel.Koebe

/-- **Change of variable `v ↦ v⁻¹` for circle integrals.**  Integrating `(v^2)⁻¹ * h v⁻¹` over the
circle of radius `r⁻¹` about `0` is the same as integrating `h` over the circle of radius `r`:
the substitution `v = w⁻¹` maps `|w| = r` to `|v| = r⁻¹`, reverses the orientation (`dθ ↦ -dθ`)
and produces the Jacobian factor `(v^2)⁻¹`; the two orientation reversals cancel. -/
theorem circleIntegral_comp_inv {h : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hh : ContinuousOn h (Metric.sphere (0 : ℂ) r)) :
    circleIntegral (fun v : ℂ => (v ^ 2)⁻¹ * h v⁻¹) 0 r⁻¹ = circleIntegral h 0 r := by
  simp only [circleIntegral, smul_eq_mul]
  trans ∫ θ in (0 : ℝ)..2 * Real.pi, deriv (circleMap 0 r) (-θ) * h (circleMap 0 r (-θ))
  · -- pointwise identity: the integrand of the left side is the right integrand at `-θ`
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hkey : circleMap 0 r⁻¹ θ = (circleMap 0 r (-θ))⁻¹ := by
      simpa using (circleMap_zero_inv r (-θ)).symm
    rw [deriv_circleMap, deriv_circleMap, hkey]
    have ha : circleMap 0 r (-θ) ≠ 0 := by
      rw [circleMap_zero]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (Complex.exp_ne_zero _)
    simp only [inv_pow, inv_inv]
    field_simp
  · -- the substitution `θ ↦ -θ` plus `2π`-periodicity of the integrand
    rw [intervalIntegral.integral_comp_neg
      (fun w : ℝ => deriv (circleMap 0 r) w * h (circleMap 0 r w))]
    have t₀ : Function.Periodic (fun w : ℝ => deriv (circleMap 0 r) w * h (circleMap 0 r w))
        (2 * Real.pi) := by
      intro x
      simp only [deriv_circleMap]
      rw [periodic_circleMap 0 r x]
    simpa using (t₀.intervalIntegral_add_eq (-(2 * Real.pi)) 0)

end Work.Repel.Koebe

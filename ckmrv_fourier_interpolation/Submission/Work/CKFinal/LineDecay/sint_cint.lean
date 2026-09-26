import Mathlib

open MeasureTheory

namespace Work.CKFinal.LineDecay

/-- The elementary interpolation identity behind the decay estimate:
`k * ∫_0^1 (1 - s) cos (s k) ds = ∫_0^1 sin (k x) dx`.

It is proved without any division: the integrand
`k (1 - s) cos (s k) - sin (k s)` is the derivative of `s ↦ (1 - s) sin (k s)`,
whose values at `0` and `1` both vanish. -/
theorem sint_cint (k : ℝ) : k * (∫ s in (0:ℝ)..1, (1 - s) * Real.cos (s * k)) = ∫ x in (0:ℝ)..1, Real.sin (k * x) := by
  -- The difference of the two integrands is the derivative of a function vanishing at both ends.
  have hderiv : ∀ y ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun y : ℝ => (1 - y) * Real.sin (k * y))
        (k * (1 - y) * Real.cos (y * k) - Real.sin (k * y)) y := by
    intro y hy
    have h1 : HasDerivAt (fun y : ℝ => Real.sin (k * y)) (Real.cos (k * y) * k) y := by
      simpa using ((hasDerivAt_id y).const_mul k).sin
    have h2 : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub 1
    have h3 := h2.mul h1
    rw [show (-1 : ℝ) * Real.sin (k * y) + (1 - y) * (Real.cos (k * y) * k)
        = k * (1 - y) * Real.cos (y * k) - Real.sin (k * y) from by
      rw [show Real.cos (k * y) = Real.cos (y * k) from by rw [mul_comm]]; ring] at h3
    exact h3
  have hcont : Continuous fun y : ℝ => k * (1 - y) * Real.cos (y * k) - Real.sin (k * y) := by
    fun_prop
  have hint : IntervalIntegrable
      (fun y : ℝ => k * (1 - y) * Real.cos (y * k) - Real.sin (k * y)) volume (0:ℝ) 1 :=
    hcont.intervalIntegrable 0 1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1) hderiv hint
  -- the primitive vanishes at both endpoints
  have hzero : (∫ y in (0:ℝ)..1, (k * (1 - y) * Real.cos (y * k) - Real.sin (k * y))) = 0 := by
    rw [hFTC]
    simp
  have hfint : IntervalIntegrable (fun y : ℝ => k * (1 - y) * Real.cos (y * k)) volume (0:ℝ) 1 :=
    (by fun_prop : Continuous fun y : ℝ => k * (1 - y) * Real.cos (y * k)).intervalIntegrable 0 1
  have hgint : IntervalIntegrable (fun y : ℝ => Real.sin (k * y)) volume (0:ℝ) 1 :=
    (by fun_prop : Continuous fun y : ℝ => Real.sin (k * y)).intervalIntegrable 0 1
  -- split the integral of the difference into the difference of the integrals
  have hfsplit : (∫ y in (0:ℝ)..1, (k * (1 - y) * Real.cos (y * k) - Real.sin (k * y)))
      = k * (∫ y in (0:ℝ)..1, (1 - y) * Real.cos (y * k))
        - (∫ y in (0:ℝ)..1, Real.sin (k * y)) := by
    rw [intervalIntegral.integral_sub hfint hgint]
    congr 1
    rw [show (∫ y in (0:ℝ)..1, k * (1 - y) * Real.cos (y * k))
          = k * ∫ y in (0:ℝ)..1, (1 - y) * Real.cos (y * k) from by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      ext y
      ring]
  have hkey : k * (∫ y in (0:ℝ)..1, (1 - y) * Real.cos (y * k))
      - (∫ y in (0:ℝ)..1, Real.sin (k * y)) = 0 := by
    rw [← hfsplit]
    exact hzero
  exact sub_eq_zero.mp hkey

end Work.CKFinal.LineDecay

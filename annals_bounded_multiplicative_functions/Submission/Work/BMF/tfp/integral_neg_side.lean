import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.tfp

open MeasureTheory intervalIntegral

/-- The left half of the Fourier integral of the triangle function `x ↦ (1-|x|)`: for `c ≠ 0`,
`∫_{x=-1}^{0} (1-|x|) e^{cx} dx = 1/c - 1/c² + e^{-c}/c²`.  On `[-1,0]` one has `1-|x| = 1+x`,
and `x ↦ ((1+x)/c - 1/c²)·e^{cx}` is an antiderivative of `x ↦ (1+x)e^{cx}`, giving
`((1/c - 1/c²)) - (-e^{-c}/c²)`.  Route: `intervalIntegral.integral_congr` (replace `1-|x|` by
`1+x` using `abs_of_nonpos`) then `intervalIntegral.integral_eq_sub_of_hasDerivAt`. -/
lemma integral_neg_side (c : ℂ) (hc : c ≠ 0) :
    ∫ x in (-1:ℝ)..0, (((1 - |x| : ℝ) : ℂ) * Complex.exp (c * (x:ℂ))) =
      1/c - 1/c^2 + Complex.exp (-c)/c^2 := by
  -- Replace `1 - |x|` by `1 + x` on `[-1, 0]`.
  have hcongr : (∫ x in (-1:ℝ)..0, (((1 - |x| : ℝ) : ℂ) * Complex.exp (c * (x:ℂ))))
      = ∫ x in (-1:ℝ)..0, ((((1 + x : ℝ)) : ℂ) * Complex.exp (c * (x:ℂ))) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hxle : x ≤ 0 := by
      rcases Set.mem_uIcc.mp hx with ⟨_, h⟩ | ⟨_, h⟩
      · exact h
      · linarith
    dsimp only
    rw [abs_of_nonpos hxle, sub_neg_eq_add]
  rw [hcongr]
  -- Antiderivative of `x ↦ (1 + x) e^{cx}`.
  have hderiv : ∀ x ∈ Set.uIcc (-1:ℝ) 0,
      HasDerivAt (fun y : ℝ => ((1 + (y:ℂ))/c - 1/c^2) * Complex.exp (c*(y:ℂ)))
        ((((1 + x : ℝ)) : ℂ) * Complex.exp (c * (x:ℂ))) x := by
    intro x hx
    have h_ofReal : HasDerivAt (fun y : ℝ => (y:ℂ)) 1 x := by
      simpa using (hasDerivAt_id (x:ℂ)).comp_ofReal
    have hu : HasDerivAt (fun y : ℝ => (1 + (y:ℂ))/c - 1/c^2) (1/c) x := by
      have h2 : HasDerivAt (fun y : ℝ => (1 + (y:ℂ))/c) (1/c) x := by
        simpa using (h_ofReal.const_add 1).div_const c
      simpa using h2.sub_const (1/c^2)
    have hv : HasDerivAt (fun y : ℝ => Complex.exp (c*(y:ℂ)))
        (c * Complex.exp (c*(x:ℂ))) x := by
      have h_inner : HasDerivAt (fun y : ℝ => c*(y:ℂ)) (c) x := by
        simpa using h_ofReal.const_mul c
      have hh := h_inner.cexp
      simpa [mul_comm] using hh
    have hF := hu.mul hv
    refine hF.congr_deriv ?_
    rw [show (((1 + x : ℝ)) : ℂ) = 1 + (x:ℂ) by push_cast; ring]
    field_simp
    ring
  have hint : IntervalIntegrable
      (fun x : ℝ => ((((1 + x : ℝ)) : ℂ) * Complex.exp (c * (x:ℂ)))) volume (-1) 0 := by
    apply Continuous.intervalIntegrable
    continuity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  -- Evaluate the antiderivative at the two endpoints.
  simp only [Complex.ofReal_zero, Complex.ofReal_neg, Complex.ofReal_one, mul_zero,
    Complex.exp_zero, mul_one, add_neg_cancel]
  field_simp
  ring

end Work.BMF.tfp

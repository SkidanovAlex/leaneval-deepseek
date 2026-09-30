import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.tfp

open MeasureTheory intervalIntegral

/-- The right half of the Fourier integral of the triangle function `x ↦ (1-|x|)`: for `c ≠ 0`,
`∫_{x=0}^{1} (1-|x|) e^{cx} dx = e^{c}/c² - 1/c - 1/c²`.  On `[0,1]` one has `1-|x| = 1-x`,
and `x ↦ ((1-x)/c + 1/c²)·e^{cx}` is an antiderivative of `x ↦ (1-x)e^{cx}`, giving
`e^{c}/c² - (1/c + 1/c²)`.  Route: `intervalIntegral.integral_congr` (replace `1-|x|` by
`1-x` using `abs_of_nonneg`) then `intervalIntegral.integral_eq_sub_of_hasDerivAt`. -/
lemma integral_pos_side (c : ℂ) (hc : c ≠ 0) :
    ∫ x in (0:ℝ)..1, (((1 - |x| : ℝ) : ℂ) * Complex.exp (c * (x:ℂ))) =
      Complex.exp c / c^2 - 1/c - 1/c^2 := by
  -- Step 1: on `[0,1]`, `1 - |x| = 1 - x`.
  have hcongr : ∫ x in (0:ℝ)..1, (((1 - |x| : ℝ) : ℂ) * Complex.exp (c * (x:ℂ)))
      = ∫ x in (0:ℝ)..1, (((1 - x : ℝ) : ℂ) * Complex.exp (c * (x:ℂ))) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : 0 ≤ x := by
      simp only [Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num), Set.mem_Icc] at hx
      exact hx.1
    simp only [abs_of_nonneg hx']
  rw [hcongr]
  -- Step 2: the antiderivative `F x = ((1-x)/c + 1/c²)·e^{cx}`.
  set F : ℝ → ℂ := fun x => (((1 - x : ℝ) : ℂ) / c + 1 / c^2) * Complex.exp (c * (x:ℂ)) with hF
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt F ((((1 - x : ℝ) : ℂ)) * Complex.exp (c * (x:ℂ))) x := by
    intro x _
    have hA : HasDerivAt (fun y : ℝ => ((1 - y : ℝ) : ℂ)) (-1) x := by
      have h1 : HasDerivAt (fun y : ℝ => (1:ℝ) - y) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub (1:ℝ)
      simpa using h1.ofReal_comp
    have hAc : HasDerivAt (fun y : ℝ => ((1 - y : ℝ) : ℂ)/c) ((-1)/c) x := hA.div_const c
    have hF1 : HasDerivAt (fun y : ℝ => ((1 - y : ℝ) : ℂ)/c + 1/c^2) ((-1)/c) x :=
      hAc.add_const (1/c^2)
    have hcx : HasDerivAt (fun y : ℝ => c * (y:ℂ)) c x := by
      have h2 : HasDerivAt (fun y : ℝ => ((y:ℂ))) 1 x := by
        simpa using (hasDerivAt_id x).ofReal_comp
      simpa using h2.const_mul c
    have hE : HasDerivAt (fun y : ℝ => Complex.exp (c * (y:ℂ))) (Complex.exp (c*(x:ℂ)) * c) x :=
      (Complex.hasDerivAt_exp (c*(x:ℂ))).comp x hcx
    have hmul := hF1.mul hE
    have hkey : ((-1:ℂ)/c) * Complex.exp (c*(x:ℂ))
          + (((1 - x : ℝ) : ℂ)/c + 1/c^2) * (Complex.exp (c*(x:ℂ)) * c)
        = (((1 - x : ℝ) : ℂ)) * Complex.exp (c*(x:ℂ)) := by
      field_simp
      ring
    rw [hF]
    rw [hkey] at hmul
    exact hmul
  have hint : IntervalIntegrable (fun x : ℝ => (((1 - x : ℝ) : ℂ) * Complex.exp (c * (x:ℂ))))
      volume (0:ℝ) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [hF]
  simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    Complex.ofReal_sub]
  ring_nf

end Work.BMF.tfp

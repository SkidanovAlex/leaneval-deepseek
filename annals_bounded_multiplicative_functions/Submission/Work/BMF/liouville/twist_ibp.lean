import Mathlib
import Submission.Work.BMF.liouville.twist_small_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open Real

/-- `Hwderiv` is continuous away from `0`. -/
lemma continuousAt_Hwderiv {s : ℝ} (hs : s ≠ 0) : ContinuousAt Hwderiv s := by
  unfold Hwderiv
  fun_prop (disch := first | exact pow_ne_zero _ hs | positivity)

/-- The real derivative of `t ↦ Hw (log t)`, pushed forward to `ℂ`:
`d/dt Hw(log t) = Hwderiv(log t) / t`. -/
lemma hasDerivAt_ofReal_Hw_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t : ℝ => ((Hw (Real.log t)) : ℂ))
      (((Hwderiv (Real.log t)) : ℂ) / t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have h1 : HasDerivAt (fun t : ℝ => Hw (Real.log t))
      (Hwderiv (Real.log t) * t⁻¹) t :=
    (hasDerivAt_Hw hlt).comp t (Real.hasDerivAt_log ht0)
  have h2 := h1.ofReal_comp
  convert h2 using 1
  push_cast
  ring

/-- Derivative of the oscillating antiderivative: for `x ≠ 0`,
`d/dt (t^{-iu} / (-iu)) = t^{-1-iu}`.  This is the complex-power derivative
`hasDerivAt_ofReal_cpow_const'` with exponent `r = -1 - iu` (so that `r + 1 = -iu`),
which requires `u ≠ 0`. -/
lemma hasDerivAt_cpow_div (u : ℝ) (hu : u ≠ 0) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => (t:ℂ) ^ (-(Complex.I * (u:ℂ))) / (-(Complex.I * (u:ℂ))))
      ((x:ℂ) ^ (-(1:ℂ) - Complex.I * (u:ℂ))) x := by
  have hr : (-(1:ℂ) - Complex.I * (u:ℂ)) ≠ -1 := by
    intro h
    have hI : Complex.I * (u:ℂ) = 0 := by linear_combination -h
    have : (u:ℂ) = 0 := (mul_eq_zero.mp hI).resolve_left Complex.I_ne_zero
    exact hu (Complex.ofReal_eq_zero.mp this)
  have hd := hasDerivAt_ofReal_cpow_const' (x := x) hx (r := -(1:ℂ) - Complex.I * (u:ℂ)) hr
  convert hd using 1
  ext y
  have : -(1:ℂ) - Complex.I * (u:ℂ) + 1 = -(Complex.I * (u:ℂ)) := by ring
  rw [this]

theorem twist_ibp (u : ℝ) (hu : u ≠ 0) {a b : ℝ} (h3 : 3 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, (t:ℂ) ^ (-(1:ℂ) - Complex.I * (u:ℂ)) * ((Work.BMF.liouville.Hw (Real.log t)) : ℂ)
      = (b:ℂ) ^ (-(Complex.I * (u:ℂ))) / (-(Complex.I * (u:ℂ))) * ((Work.BMF.liouville.Hw (Real.log b)) : ℂ)
        - (a:ℂ) ^ (-(Complex.I * (u:ℂ))) / (-(Complex.I * (u:ℂ))) * ((Work.BMF.liouville.Hw (Real.log a)) : ℂ)
        - ∫ t in a..b, ((t:ℂ) ^ (-(Complex.I * (u:ℂ))) / (-(Complex.I * (u:ℂ)))) *
            ((Work.BMF.liouville.Hwderiv (Real.log t)) : ℂ) / t := by
  set F : ℝ → ℂ := fun t => (t:ℂ) ^ (-(Complex.I * (u:ℂ))) / (-(Complex.I * (u:ℂ))) with hF
  set F' : ℝ → ℂ := fun t => (t:ℂ) ^ (-(1:ℂ) - Complex.I * (u:ℂ)) with hF'
  set G : ℝ → ℂ := fun t => ((Hw (Real.log t)) : ℂ) with hG
  set G' : ℝ → ℂ := fun t => ((Hwderiv (Real.log t)) : ℂ) / t with hG'
  have hderiv_F : ∀ x ∈ Set.uIcc a b, HasDerivAt F (F' x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1, h3]
    rw [hF, hF']
    exact hasDerivAt_cpow_div u hu hx0
  have hderiv_G : ∀ x ∈ Set.uIcc a b, HasDerivAt G (G' x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx1 : 1 < x := by linarith [hx.1, h3]
    rw [hG, hG']
    exact hasDerivAt_ofReal_Hw_log hx1
  have hint_F : IntervalIntegrable F' MeasureTheory.volume a b := by
    rw [hF']
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1, h3]
    exact (Complex.continuousAt_ofReal_cpow_const x _ (Or.inr hx0)).continuousWithinAt
  have hint_G : IntervalIntegrable G' MeasureTheory.volume a b := by
    rw [hG']
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1, h3]
    have hx1 : 1 < x := by linarith [hx.1, h3]
    have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
    have hlogc : ContinuousWithinAt (fun t : ℝ => Real.log t) (Set.uIcc a b) x :=
      (Real.continuousAt_log hx0).continuousWithinAt
    have hnum : ContinuousWithinAt (fun t : ℝ => ((Hwderiv (Real.log t)) : ℂ)) (Set.uIcc a b) x :=
      Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
        ((continuousAt_Hwderiv hlog).comp_continuousWithinAt hlogc)
    have hden : ContinuousWithinAt (fun t : ℝ => (t:ℂ)) (Set.uIcc a b) x :=
      Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt continuousWithinAt_id
    exact hnum.div hden (by exact_mod_cast hx0)
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hderiv_G hderiv_F hint_G hint_F
  trans ∫ x in a..b, G x * F' x
  · apply intervalIntegral.integral_congr
    intro x hx
    simp only [G, F']
    exact mul_comm _ _
  · rw [key]
    have hI : (∫ x in a..b, G' x * F x)
        = ∫ x in a..b, ((x:ℂ) ^ (-(Complex.I * (u:ℂ))) / (-(Complex.I * (u:ℂ)))) *
            ((Hwderiv (Real.log x)) : ℂ) / x := by
      apply intervalIntegral.integral_congr
      intro x hx
      simp only [G', F]
      ring
    rw [hI]
    simp only [G, F]
    ring

end Work.BMF.liouville

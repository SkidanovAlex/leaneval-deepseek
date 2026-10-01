import Mathlib
import Submission.Commons.Analysis.Integral.integral_div_sq_add_sq_sq
import Submission.Commons.Analysis.Integral.integral_inv_sq_add
import Submission.Commons.Analysis.Real.arsinh_log_bounds
import Submission.Commons.Analysis.Real.log_one_add_le_half_add

open MeasureTheory intervalIntegral

namespace Commons.Analysis.Integral

/-! ### Kernel integrals on `[1/4,1/2]` -/

/-- `∫_{1/4}^{1/2} c/(c²+s²) ds = arctan(1/(2c)) - arctan(1/(4c))`. -/
theorem integral_kernel_interval {c : ℝ} (hc : 0 < c) :
    (∫ s in (1/4:ℝ)..(1/2), c/(c^2+s^2))
      = Real.arctan (1/(2*c)) - Real.arctan (1/(4*c)) := by
  rw [integral_inv_sq_add hc]
  have h1 : (1/2 : ℝ)/c = 1/(2*c) := by field_simp
  have h2 : (1/4 : ℝ)/c = 1/(4*c) := by field_simp
  rw [h1, h2]

/-- `∫_{1/4}^{1/2} 1/(c²+s²)² ds`. -/
theorem integral_kernel_sq_interval {c : ℝ} (hc : 0 < c) :
    (∫ s in (1/4:ℝ)..(1/2), 1/(c^2+s^2)^2)
      = (1/c)*( (1/2)/(2*c*(c^2+1/4)) - (1/4)/(2*c*(c^2+1/16))
          + (Real.arctan (1/(2*c)) - Real.arctan (1/(4*c)))/(2*c^2) ) := by
  have h := integral_div_sq_add_sq_sq (a := (1/4:ℝ)) (b := (1/2:ℝ)) hc
  have heq : (∫ s in (1/4:ℝ)..(1/2), 1/(c^2+s^2)^2)
      = (1/c) * (∫ s in (1/4:ℝ)..(1/2), c/(c^2+s^2)^2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    field_simp
  rw [heq, h]
  have h1 : (1/2 : ℝ)/c = 1/(2*c) := by field_simp
  have h2 : (1/4 : ℝ)/c = 1/(4*c) := by field_simp
  rw [h1, h2]
  field_simp
  ring

/-- Antiderivative of `t ↦ (c²+t²)⁻³`. -/
theorem hasDerivAt_inv_sq_add_sq_cube {c : ℝ} (hc : 0 < c) (x : ℝ) :
    HasDerivAt (fun t : ℝ => t*(5*c^2+3*t^2)/(8*c^4*(c^2+t^2)^2) + 3*Real.arctan (t/c)/(8*c^5))
      (1/(c^2+x^2)^3) x := by
  have hnum : HasDerivAt (fun t : ℝ => t*(5*c^2+3*t^2)) (5*c^2+9*x^2) x := by
    have ha : HasDerivAt (fun t : ℝ => t) (1:ℝ) x := hasDerivAt_id x
    have hb : HasDerivAt (fun t : ℝ => 5*c^2+3*t^2) (6*x) x := by
      have h : HasDerivAt (fun t : ℝ => t^2) (2*x) x := by simpa using hasDerivAt_pow 2 x
      have h2 := (h.const_mul (3:ℝ)).const_add (5*c^2)
      refine h2.congr_deriv ?_
      ring
    exact (ha.mul hb).congr_deriv (by ring)
  have hden : HasDerivAt (fun t : ℝ => 8*c^4*(c^2+t^2)^2) (8*c^4*(2*(c^2+x^2)*(2*x))) x := by
    have h : HasDerivAt (fun t : ℝ => c^2+t^2) (2*x) x := by
      have hh : HasDerivAt (fun t : ℝ => t^2) (2*x) x := by simpa using hasDerivAt_pow 2 x
      simpa using hh.const_add (c^2)
    have h2 := (h.pow 2).const_mul (8*c^4)
    simpa using h2
  have h1 : HasDerivAt (fun t : ℝ => t*(5*c^2+3*t^2)/(8*c^4*(c^2+t^2)^2))
      ((5*c^2+9*x^2)/(8*c^4*(c^2+x^2)^2) - x*(5*c^2+3*x^2)*(2*x)/(4*c^4*(c^2+x^2)^3)) x := by
    have h := hnum.div hden (by positivity)
    refine h.congr_deriv ?_
    field_simp
    ring
  have h2 : HasDerivAt (fun t : ℝ => 3*Real.arctan (t/c)/(8*c^5)) (3/(8*c^4*(c^2+x^2))) x := by
    have hin : HasDerivAt (fun t : ℝ => t/c) (1/c) x := (hasDerivAt_id x).div_const c
    have h := ((Real.hasDerivAt_arctan (x/c)).comp x hin).const_mul (3:ℝ) |>.div_const (8*c^5)
    refine h.congr_deriv ?_
    field_simp
  have h := h1.add h2
  refine h.congr_deriv ?_
  field_simp
  ring

/-- `∫_{a}^{b} (c²+t²)⁻³ dt`. -/
theorem integral_inv_sq_add_sq_cube {c a b : ℝ} (hc : 0 < c) :
    (∫ t in a..b, 1/(c^2+t^2)^3)
      = (b*(5*c^2+3*b^2)/(8*c^4*(c^2+b^2)^2) - a*(5*c^2+3*a^2)/(8*c^4*(c^2+a^2)^2))
        + 3*(Real.arctan (b/c) - Real.arctan (a/c))/(8*c^5) := by
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => t*(5*c^2+3*t^2)/(8*c^4*(c^2+t^2)^2) + 3*Real.arctan (t/c)/(8*c^5))
        (1/(c^2+x^2)^3) x := fun x _ => hasDerivAt_inv_sq_add_sq_cube hc x
  have hcont : Continuous (fun t : ℝ => 1/(c^2+t^2)^3) := by
    apply Continuous.div continuous_const
    · fun_prop
    · intro t; positivity
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => t*(5*c^2+3*t^2)/(8*c^4*(c^2+t^2)^2) + 3*Real.arctan (t/c)/(8*c^5))
    (f' := fun t : ℝ => 1/(c^2+t^2)^3) hderiv (hcont.intervalIntegrable a b)
  rw [h]
  field_simp
  ring


/-! ### The target kernel and its integral -/

/-- The positive part `T` of the integrand. -/
noncomputable def Tterm (β : ℝ) (s : ℝ) : ℝ :=
  (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
    + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
    + ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
    + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3)

/-- `arctan (1/(2(3/2-β))) - arctan (1/(4(3/2-β)))`. -/
noncomputable def FA (β : ℝ) : ℝ :=
  Real.arctan (1/(2*(3/2-β))) - Real.arctan (1/(4*(3/2-β)))

/-- `arctan (1/(2(1+β))) - arctan (1/(4(1+β)))`. -/
noncomputable def FB (β : ℝ) : ℝ :=
  Real.arctan (1/(2*(1+β))) - Real.arctan (1/(4*(1+β)))

/-- `arctan (1/(2(2-β))) - arctan (1/(4(2-β)))`. -/
noncomputable def FD (β : ℝ) : ℝ :=
  Real.arctan (1/(2*(2-β))) - Real.arctan (1/(4*(2-β)))

/-- The coefficient multiplying `FD` in `∫ T`. -/
noncomputable def Ctot (β : ℝ) : ℝ :=
  ((2-β)^2-β^2)/(2*(2-β)) + ((2-β)^2-β^2)^2/(16*(2-β)^3)
    + 3*((2-β)^2-β^2)^3/(128*(2-β)^5)

/-- Rational part of the `(A²+s²)⁻²` integral contribution. -/
noncomputable def P4r (β : ℝ) : ℝ :=
  ((2-β)^2-β^2)^2/8*( (1/2)/(2*(2-β)^2*((2-β)^2+1/4))
    - (1/4)/(2*(2-β)^2*((2-β)^2+1/16)) )

/-- Rational part of the `(A²+s²)⁻³` integral contribution. -/
noncomputable def P5r (β : ℝ) : ℝ :=
  ((2-β)^2-β^2)^3/16*( (1/2)*(5*(2-β)^2+3/4)/(8*(2-β)^4*((2-β)^2+1/4)^2)
    - (1/4)*(5*(2-β)^2+3/16)/(8*(2-β)^4*((2-β)^2+1/16)^2) )

theorem integral_T_term {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∫ s in (1/4:ℝ)..(1/2), Tterm β s)
      = (13/5)*(FA β + FB β) + Ctot β * FD β + P4r β + P5r β := by
  have hA : (0:ℝ) < 2 - β := by linarith
  have h1 : (0:ℝ) < 3/2 - β := by linarith
  have h2 : (0:ℝ) < 1 + β := by linarith
  have hcA : Continuous fun s : ℝ => ((3/2-β) : ℝ)/((3/2-β)^2+s^2) :=
    (continuous_const (y := ((3/2-β):ℝ))).div (by fun_prop) (by intro s; positivity)
  have hcB : Continuous fun s : ℝ => ((1+β) : ℝ)/((1+β)^2+s^2) :=
    (continuous_const (y := ((1+β):ℝ))).div (by fun_prop) (by intro s; positivity)
  have hcAB : Continuous fun s : ℝ => (13/5)*(((3/2-β)/((3/2-β)^2+s^2))+((1+β)/((1+β)^2+s^2))) :=
    Continuous.const_mul (hcA.add hcB) _
  have hc1 : Continuous fun s : ℝ => (((2-β)^2-β^2) : ℝ)/(2*((2-β)^2+s^2)) :=
    (continuous_const (y := ((2-β)^2-β^2 : ℝ))).div (by fun_prop) (by intro s; positivity)
  have hc2 : Continuous fun s : ℝ => (((2-β)^2-β^2)^2 : ℝ)/(8*((2-β)^2+s^2)^2) :=
    (continuous_const (y := (((2-β)^2-β^2)^2 : ℝ))).div (by fun_prop) (by intro s; positivity)
  have hc3 : Continuous fun s : ℝ => (((2-β)^2-β^2)^3 : ℝ)/(16*((2-β)^2+s^2)^3) :=
    (continuous_const (y := (((2-β)^2-β^2)^3 : ℝ))).div (by fun_prop) (by intro s; positivity)
  have hsplit : (∫ s in (1/4:ℝ)..(1/2), Tterm β s)
      = (∫ s in (1/4:ℝ)..(1/2), (13/5)*(((3/2-β)/((3/2-β)^2+s^2))+((1+β)/((1+β)^2+s^2))))
        + (∫ s in (1/4:ℝ)..(1/2), (((2-β)^2-β^2) : ℝ)/(2*((2-β)^2+s^2)))
        + (∫ s in (1/4:ℝ)..(1/2), (((2-β)^2-β^2)^2 : ℝ)/(8*((2-β)^2+s^2)^2))
        + (∫ s in (1/4:ℝ)..(1/2), (((2-β)^2-β^2)^3 : ℝ)/(16*((2-β)^2+s^2)^3)) := by
    have e : Tterm β = fun s : ℝ =>
        (13/5)*(((3/2-β)/((3/2-β)^2+s^2))+((1+β)/((1+β)^2+s^2)))
          + (((2-β)^2-β^2) : ℝ)/(2*((2-β)^2+s^2))
          + (((2-β)^2-β^2)^2 : ℝ)/(8*((2-β)^2+s^2)^2)
          + (((2-β)^2-β^2)^3 : ℝ)/(16*((2-β)^2+s^2)^3) := by
      funext s; simp only [Tterm]
    rw [e]
    rw [intervalIntegral.integral_add
      (f := fun s : ℝ => (13/5)*(((3/2-β)/((3/2-β)^2+s^2))+((1+β)/((1+β)^2+s^2)))
          + (((2-β)^2-β^2) : ℝ)/(2*((2-β)^2+s^2)) + (((2-β)^2-β^2)^2 : ℝ)/(8*((2-β)^2+s^2)^2))
      (g := fun s : ℝ => (((2-β)^2-β^2)^3 : ℝ)/(16*((2-β)^2+s^2)^3))
      (((hcAB.add hc1).add hc2).intervalIntegrable _ _) (hc3.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_add
      (f := fun s : ℝ => (13/5)*(((3/2-β)/((3/2-β)^2+s^2))+((1+β)/((1+β)^2+s^2)))
          + (((2-β)^2-β^2) : ℝ)/(2*((2-β)^2+s^2)))
      (g := fun s : ℝ => (((2-β)^2-β^2)^2 : ℝ)/(8*((2-β)^2+s^2)^2))
      ((hcAB.add hc1).intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_add
      (f := fun s : ℝ => (13/5)*(((3/2-β)/((3/2-β)^2+s^2))+((1+β)/((1+β)^2+s^2))))
      (g := fun s : ℝ => (((2-β)^2-β^2) : ℝ)/(2*((2-β)^2+s^2)))
      (hcAB.intervalIntegrable _ _) (hc1.intervalIntegrable _ _)]
  rw [hsplit]
  clear hsplit
  have hs1 : (∫ s in (1/4:ℝ)..(1/2), (13/5)*(((3/2-β)/((3/2-β)^2+s^2))+((1+β)/((1+β)^2+s^2))))
      = (13/5)*((Real.arctan (1/(2*(3/2-β))) - Real.arctan (1/(4*(3/2-β))))
                + (Real.arctan (1/(2*(1+β))) - Real.arctan (1/(4*(1+β))))) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    rw [intervalIntegral.integral_add (f := fun s : ℝ => ((3/2-β) : ℝ)/((3/2-β)^2+s^2))
      (g := fun s : ℝ => ((1+β) : ℝ)/((1+β)^2+s^2))
      (hcA.intervalIntegrable _ _) (hcB.intervalIntegrable _ _)]
    congr 1
    · exact integral_kernel_interval h1
    · exact integral_kernel_interval h2
  have hs2 : (∫ s in (1/4:ℝ)..(1/2), (((2-β)^2-β^2) : ℝ)/(2*((2-β)^2+s^2)))
      = ((2-β)^2-β^2)/(2*(2-β)) * (Real.arctan (1/(2*(2-β))) - Real.arctan (1/(4*(2-β)))) := by
    have heq : (∫ s in (1/4:ℝ)..(1/2), (((2-β)^2-β^2) : ℝ)/(2*((2-β)^2+s^2)))
        = (((2-β)^2-β^2)/(2*(2-β))) * (∫ s in (1/4:ℝ)..(1/2), (2-β)/((2-β)^2+s^2)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      field_simp
    rw [heq, integral_kernel_interval hA]
  have hs3 : (∫ s in (1/4:ℝ)..(1/2), (((2-β)^2-β^2)^2 : ℝ)/(8*((2-β)^2+s^2)^2))
      = ((2-β)^2-β^2)^2/8*( (1/2)/(2*(2-β)^2*((2-β)^2+1/4))
          - (1/4)/(2*(2-β)^2*((2-β)^2+1/16)) )
        + ((2-β)^2-β^2)^2/(16*(2-β)^3)*(Real.arctan (1/(2*(2-β))) - Real.arctan (1/(4*(2-β)))) := by
    have heq : (∫ s in (1/4:ℝ)..(1/2), (((2-β)^2-β^2)^2 : ℝ)/(8*((2-β)^2+s^2)^2))
        = (((2-β)^2-β^2)^2/8) * (∫ s in (1/4:ℝ)..(1/2), 1/((2-β)^2+s^2)^2) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      field_simp
    rw [heq, integral_kernel_sq_interval hA]
    field_simp
    ring
  have hs4 : (∫ s in (1/4:ℝ)..(1/2), (((2-β)^2-β^2)^3 : ℝ)/(16*((2-β)^2+s^2)^3))
      = ((2-β)^2-β^2)^3/16*( (1/2)*(5*(2-β)^2+3/4)/(8*(2-β)^4*((2-β)^2+1/4)^2)
          - (1/4)*(5*(2-β)^2+3/16)/(8*(2-β)^4*((2-β)^2+1/16)^2) )
        + 3*((2-β)^2-β^2)^3/(128*(2-β)^5)*(Real.arctan (1/(2*(2-β))) - Real.arctan (1/(4*(2-β)))) := by
    have heq : (∫ s in (1/4:ℝ)..(1/2), (((2-β)^2-β^2)^3 : ℝ)/(16*((2-β)^2+s^2)^3))
        = (((2-β)^2-β^2)^3/16) * (∫ s in (1/4:ℝ)..(1/2), 1/((2-β)^2+s^2)^3) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      field_simp
    rw [heq, integral_inv_sq_add_sq_cube hA]
    have h1' : (1/2:ℝ)/(2-β) = 1/(2*(2-β)) := by field_simp
    have h2' : (1/4:ℝ)/(2-β) = 1/(4*(2-β)) := by field_simp
    rw [h1', h2']
    field_simp
    ring
  rw [hs1, hs2, hs3, hs4]
  rw [FA, FB, FD, Ctot, P4r, P5r]
  field_simp
  ring


/-! ### Elementary integrals over `[1/4,1/2]` -/

lemma integral_sq_14_12 : (∫ s in (1/4:ℝ)..(1/2), s^2) = 7/192 := by
  rw [integral_pow]; norm_num

lemma integral_sq4_14_12 : (∫ s in (1/4:ℝ)..(1/2), s^4) = 31/5120 := by
  rw [integral_pow]; norm_num

lemma integral_sq6_14_12 : (∫ s in (1/4:ℝ)..(1/2), s^6) = 127/114688 := by
  rw [integral_pow]; norm_num

lemma integral_sq8_14_12 : (∫ s in (1/4:ℝ)..(1/2), s^8) = 511/2359296 := by
  rw [integral_pow]; norm_num

lemma integral_log_14_12 : (∫ s in (1/4:ℝ)..(1/2), Real.log s) = -1/4 := by
  have hderiv : ∀ x ∈ Set.uIcc (1/4:ℝ) (1/2),
      HasDerivAt (fun s : ℝ => s * Real.log s - s) (Real.log x) x := by
    intro x hx
    have hx0 : x ≠ 0 := by
      have := hx; rw [Set.uIcc_of_le (by norm_num : (1/4:ℝ) ≤ 1/2)] at this
      linarith [this.1]
    have h1 : HasDerivAt (fun s : ℝ => s * Real.log s) (Real.log x + 1) x := by
      have h := (hasDerivAt_id x).mul (Real.hasDerivAt_log hx0)
      have h' : HasDerivAt (fun s : ℝ => s * Real.log s) ((1 : ℝ) * Real.log x + x * x⁻¹) x := h
      have hval : (1 : ℝ) * Real.log x + x * x⁻¹ = Real.log x + 1 := by
        rw [one_mul, mul_inv_cancel₀ hx0, add_comm]
      rwa [hval] at h'
    have h2 : HasDerivAt (fun s : ℝ => s * Real.log s - s) (Real.log x + 1 - 1) x := h1.sub (hasDerivAt_id x)
    have hval : Real.log x + 1 - 1 = Real.log x := by ring
    rwa [hval] at h2
  have hint : IntervalIntegrable (fun s : ℝ => Real.log s) volume (1/4) (1/2) :=
    intervalIntegrable_log'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have h2 : Real.log (1/4 : ℝ) = -2*Real.log 2 := by
    rw [show (1/4:ℝ) = 2^(-2:ℤ) by norm_num, Real.log_zpow]
    norm_num
  have h3 : Real.log (1/2 : ℝ) = -Real.log 2 := by
    rw [show (1/2:ℝ) = 2^(-1:ℤ) by norm_num, Real.log_zpow]; norm_num
  rw [h2, h3]; ring

lemma integral_sq_log_14_12 : (∫ s in (1/4:ℝ)..(1/2), s^2 * Real.log s)
    = -(1/32)*Real.log 2 - 7/576 := by
  have hderiv : ∀ x ∈ Set.uIcc (1/4:ℝ) (1/2),
      HasDerivAt (fun s : ℝ => s^3/3 * Real.log s - s^3/9) (x^2 * Real.log x) x := by
    intro x hx
    have hx0 : x ≠ 0 := by
      have := hx; rw [Set.uIcc_of_le (by norm_num : (1/4:ℝ) ≤ 1/2)] at this
      linarith [this.1]
    have h1 : HasDerivAt (fun s : ℝ => s^3/3) (x^2) x := by
      have h := (hasDerivAt_pow 3 x).div_const (3:ℝ)
      simpa using h
    have h2 := h1.mul (Real.hasDerivAt_log hx0)
    have h3 : HasDerivAt (fun s : ℝ => s^3/9) (x^2/3) x := by
      have h := (hasDerivAt_pow 3 x).div_const (9:ℝ)
      have he : 3 * x^2 / 9 = x^2/3 := by ring
      simpa [he] using h
    have h4 := h2.sub h3
    refine h4.congr_deriv ?_
    field_simp
    ring
  have hint : IntervalIntegrable (fun s : ℝ => s^2 * Real.log s) volume (1/4) (1/2) := by
    have h : IntervalIntegrable (fun s : ℝ => Real.log s) volume (1/4) (1/2) :=
      intervalIntegrable_log'
    exact h.continuousOn_mul (a := (1/4:ℝ)) (b := (1/2:ℝ)) (continuousOn_id.pow 2)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have h2 : Real.log (1/4 : ℝ) = -2*Real.log 2 := by
    rw [show (1/4:ℝ) = 2^(-2:ℤ) by norm_num, Real.log_zpow]; norm_num
  have h3 : Real.log (1/2 : ℝ) = -Real.log 2 := by
    rw [show (1/2:ℝ) = 2^(-1:ℤ) by norm_num, Real.log_zpow]; norm_num
  rw [h2, h3]; ring

/-! ### The arctan-difference identities -/

noncomputable def dl1 (β : ℝ) : ℝ := (3-2*β)/(8*β^2-24*β+19)
noncomputable def dl2 (β : ℝ) : ℝ := 2*(1+β)/(8*(1+β)^2+1)
noncomputable def dlr (β : ℝ) : ℝ := 2*(2-β)/(8*(2-β)^2+1)

lemma arctan_ratio_aux1 {h : ℝ} (hh : 0 < h) :
    (1:ℝ)/(2*h) + -(1/(4*h)) = 1/(4*h) := by field_simp; ring

lemma arctan_ratio_aux2 {h : ℝ} (hh : 0 < h) :
    (1:ℝ) - (1/(2*h))*(-(1/(4*h))) = (8*h^2+1)/(8*h^2) := by
  rw [mul_neg, sub_neg_eq_add]; field_simp; ring

lemma arctan_ratio_aux3 {h : ℝ} (hh : 0 < h) :
    ((1:ℝ)/(4*h))/((8*h^2+1)/(8*h^2)) = 2*h/(8*h^2+1) := by field_simp; ring

theorem FA_eq_arctan {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : FA β = Real.arctan (dl1 β) := by
  have h1 : (0:ℝ) < 3/2 - β := by linarith
  have hkey : Real.arctan (1/(2*(3/2-β))) + Real.arctan (-(1/(4*(3/2-β))))
      = Real.arctan ((1/(2*(3/2-β)) + -(1/(4*(3/2-β))))
          /(1 - (1/(2*(3/2-β)))*(-(1/(4*(3/2-β)))))) := by
    apply Real.arctan_add
    have hp : 0 < 1/(2*(3/2-β)) * (1/(4*(3/2-β))) := by positivity
    nlinarith [hp]
  rw [Real.arctan_neg] at hkey
  have hA := arctan_ratio_aux1 (h := 3/2-β) h1
  have hB := arctan_ratio_aux2 (h := 3/2-β) h1
  rw [hA, hB] at hkey
  have hC := arctan_ratio_aux3 (h := 3/2-β) h1
  rw [hC] at hkey
  have hD : 2*(3/2-β)/(8*(3/2-β)^2+1) = dl1 β := by
    rw [dl1]; congr 1 <;> ring
  rw [hD] at hkey
  rw [FA, sub_eq_add_neg]
  exact hkey

theorem FB_eq_arctan {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : FB β = Real.arctan (dl2 β) := by
  have h1 : (0:ℝ) < 1 + β := by linarith
  have hkey : Real.arctan (1/(2*(1+β))) + Real.arctan (-(1/(4*(1+β))))
      = Real.arctan ((1/(2*(1+β)) + -(1/(4*(1+β))))/(1 - (1/(2*(1+β)))*(-(1/(4*(1+β)))))) := by
    apply Real.arctan_add
    have hp : 0 < 1/(2*(1+β)) * (1/(4*(1+β))) := by positivity
    nlinarith [hp]
  rw [Real.arctan_neg] at hkey
  have hA := arctan_ratio_aux1 (h := 1+β) h1
  have hB := arctan_ratio_aux2 (h := 1+β) h1
  rw [hA, hB] at hkey
  have hC := arctan_ratio_aux3 (h := 1+β) h1
  rw [hC] at hkey
  have hD : 2*(1+β)/(8*(1+β)^2+1) = dl2 β := by rw [dl2]
  rw [hD] at hkey
  rw [FB, sub_eq_add_neg]
  exact hkey

theorem FD_eq_arctan {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : FD β = Real.arctan (dlr β) := by
  have h1 : (0:ℝ) < 2 - β := by linarith
  have hkey : Real.arctan (1/(2*(2-β))) + Real.arctan (-(1/(4*(2-β))))
      = Real.arctan ((1/(2*(2-β)) + -(1/(4*(2-β))))/(1 - (1/(2*(2-β)))*(-(1/(4*(2-β)))))) := by
    apply Real.arctan_add
    have hp : 0 < 1/(2*(2-β)) * (1/(4*(2-β))) := by positivity
    nlinarith [hp]
  rw [Real.arctan_neg] at hkey
  have hA := arctan_ratio_aux1 (h := 2-β) h1
  have hB := arctan_ratio_aux2 (h := 2-β) h1
  rw [hA, hB] at hkey
  have hC := arctan_ratio_aux3 (h := 2-β) h1
  rw [hC] at hkey
  have hD : 2*(2-β)/(8*(2-β)^2+1) = dlr β := by rw [dlr]
  rw [hD] at hkey
  rw [FD, sub_eq_add_neg]
  exact hkey

lemma cont_inv_one_add_sq : Continuous (fun t : ℝ => (1+t^2)⁻¹) := by
  have h : Continuous (fun t : ℝ => (1:ℝ) / (1 + t^2)) :=
    (continuous_const (y := (1:ℝ))).div (by fun_prop : Continuous (fun t : ℝ => 1 + t^2))
      (fun t => by positivity)
  simpa [one_div] using h

theorem log_one_sub_le_neg_partial_sum (m : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    Real.log (1 - y) ≤ - ∑ k ∈ Finset.range m, y^(k+1)/((k:ℝ)+1) := by
  set S : ℝ → ℝ := fun t : ℝ => ∑ k ∈ Finset.range m, t^(k+1)/((k:ℝ)+1) with hSdef
  have hcont : ContinuousOn (fun t : ℝ => -Real.log (1-t) - S t) (Set.Icc 0 y) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.neg
      apply ContinuousOn.log
      · fun_prop
      · intro t ht; have := ht.2; linarith
    · rw [hSdef]; fun_prop
  have hderiv : ∀ t ∈ interior (Set.Icc 0 y),
      HasDerivWithinAt (fun t : ℝ => -Real.log (1-t) - S t) (t^m/(1-t)) (interior (Set.Icc 0 y)) t := by
    intro t ht
    rw [interior_Icc] at ht
    have ht1 : t < 1 := by linarith [ht.2]
    have h1 : HasDerivAt (fun s : ℝ => -Real.log (1-s)) (1/(1-t)) t := by
      have hin : HasDerivAt (fun s : ℝ => (1:ℝ) - s) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub (1:ℝ)
      have h := (hin.log (by linarith)).neg
      refine h.congr_deriv ?_
      ring_nf
    have h3 : HasDerivAt S (∑ k ∈ Finset.range m, t^k) t := by
      rw [hSdef]
      refine HasDerivAt.fun_sum ?_
      intro k hk
      have h := (hasDerivAt_pow (k+1) t).div_const (((k:ℝ)+1))
      rw [Nat.add_sub_cancel] at h
      refine h.congr_deriv ?_
      rw [show ((k:ℝ)+1) = ((k+1:ℕ):ℝ) by push_cast; ring]
      exact mul_div_cancel_left₀ _ (by positivity)
    refine ((h1.sub h3).hasDerivWithinAt).congr_deriv ?_
    have hne : (1:ℝ) - t ≠ 0 := by linarith
    have hgeo : (∑ k ∈ Finset.range m, t^k) * (1 - t) = 1 - t^m := geom_sum_mul_neg t m
    rw [eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne, hgeo]
    ring
  have hnonneg : ∀ t ∈ interior (Set.Icc 0 y), 0 ≤ t^m/(1-t) := by
    intro t ht
    rw [interior_Icc] at ht
    have h1t : 0 < 1 - t := by linarith [ht.2, hy1]
    exact div_nonneg (pow_nonneg ht.1.le m) h1t.le
  have hmono : MonotoneOn (fun t : ℝ => -Real.log (1-t) - S t) (Set.Icc 0 y) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 y) hcont hderiv hnonneg
  have hmem0 : (0:ℝ) ∈ Set.Icc 0 y := ⟨le_refl 0, hy0⟩
  have hmem : y ∈ Set.Icc 0 y := ⟨hy0, le_refl y⟩
  have h := hmono hmem0 hmem hy0
  have hS0 : S 0 = 0 := by
    rw [hSdef]
    apply Finset.sum_eq_zero
    intro k hk
    rw [zero_pow (Nat.succ_ne_zero k)]
    simp
  have hG0 : (fun t : ℝ => -Real.log (1-t) - S t) 0 = 0 := by
    simp only [sub_zero]
    rw [Real.log_one, hS0]
    ring
  rw [hG0] at h
  rw [hSdef] at h
  linarith

/-- `log (1+u) ≤ u - u²/2 + u³/3` for `0 ≤ u ≤ 1`. -/
theorem log_one_add_le_cubic {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.log (1 + u) ≤ u - u^2/2 + u^3/3 := by
  have hcont : ContinuousOn (fun t : ℝ => t - t^2/2 + t^3/3 - Real.log (1+t)) (Set.Icc 0 u) := by
    apply ContinuousOn.sub
    · fun_prop
    · apply ContinuousOn.log
      · fun_prop
      · intro t ht; have := ht.1; linarith
  have hderiv : ∀ t ∈ interior (Set.Icc 0 u),
      HasDerivWithinAt (fun t : ℝ => t - t^2/2 + t^3/3 - Real.log (1+t)) (t^3/(1+t))
        (interior (Set.Icc 0 u)) t := by
    intro t ht
    rw [interior_Icc] at ht
    have ht1 : (0:ℝ) < 1 + t := by linarith [ht.1]
    have h1 : HasDerivAt (fun t : ℝ => t - t^2/2 + t^3/3) (1 - t + t^2) t := by
      have h2 : HasDerivAt (fun t : ℝ => t^2/2) (t) t := by
        have h := (hasDerivAt_pow 2 t).div_const (2:ℝ)
        simpa using h
      have h3 : HasDerivAt (fun t : ℝ => t^3/3) (t^2) t := by
        have h := (hasDerivAt_pow 3 t).div_const (3:ℝ)
        simpa using h
      exact ((hasDerivAt_id t).sub h2).add h3
    have h4 : HasDerivAt (fun t : ℝ => Real.log (1+t)) (1/(1+t)) t := by
      have hin : HasDerivAt (fun s : ℝ => (1:ℝ) + s) 1 t := by
        simpa using (hasDerivAt_id t).const_add (1:ℝ)
      simpa using hin.log (by linarith)
    have h5 := h1.sub h4
    refine h5.hasDerivWithinAt.congr_deriv ?_
    field_simp
    ring
  have hnonneg : ∀ t ∈ interior (Set.Icc 0 u), 0 ≤ t^3/(1+t) := by
    intro t ht
    rw [interior_Icc] at ht
    have h1t : (0:ℝ) < 1 + t := by linarith [ht.1]
    exact div_nonneg (pow_nonneg ht.1.le 3) h1t.le
  have hmono : MonotoneOn (fun t : ℝ => t - t^2/2 + t^3/3 - Real.log (1+t)) (Set.Icc 0 u) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 u) hcont hderiv hnonneg
  have hmem0 : (0:ℝ) ∈ Set.Icc 0 u := ⟨le_refl 0, hu0⟩
  have hmem : u ∈ Set.Icc 0 u := ⟨hu0, le_refl u⟩
  have h := hmono hmem0 hmem hu0
  have h0 : (fun t : ℝ => t - t^2/2 + t^3/3 - Real.log (1+t)) 0 = 0 := by
    simp [Real.log_one]
  rw [h0] at h
  have h' : 0 ≤ u - u^2/2 + u^3/3 - Real.log (1+u) := h
  linarith

/-- Alternating Taylor lower bound for `arctan` on `[0,1]`. -/
theorem arctan_taylor7_lower {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x - x^3/3 + x^5/5 - x^7/7 ≤ Real.arctan x := by
  have hcont1 : Continuous (fun t : ℝ => 1 - t^2 + t^4 - t^6) := by fun_prop
  have hmono : (∫ t in (0:ℝ)..x, (1 - t^2 + t^4 - t^6)) ≤ ∫ t in (0:ℝ)..x, (1+t^2)⁻¹ := by
    apply intervalIntegral.integral_mono_on hx0 (hcont1.intervalIntegrable _ _)
      (cont_inv_one_add_sq.intervalIntegrable _ _)
    intro t ht
    have ht1 : t ≤ 1 := le_trans ht.2 hx1
    rw [inv_eq_one_div, le_div_iff₀ (by positivity : (0:ℝ) < 1 + t^2)]
    have h : (1 - t^2 + t^4 - t^6) * (1 + t^2) = 1 - t^8 := by ring
    rw [h]
    have : 0 ≤ t^8 := by positivity
    linarith
  have hderiv : ∀ y ∈ Set.uIcc (0:ℝ) x,
      HasDerivAt (fun t : ℝ => t - t^3/3 + t^5/5 - t^7/7) (1 - y^2 + y^4 - y^6) y := by
    intro y _
    have h1 : HasDerivAt (fun t : ℝ => t) 1 y := hasDerivAt_id y
    have h3 : HasDerivAt (fun t : ℝ => t^3/3) (y^2) y := by
      have h := (hasDerivAt_pow 3 y).div_const (3:ℝ); simpa using h
    have h5 : HasDerivAt (fun t : ℝ => t^5/5) (y^4) y := by
      have h := (hasDerivAt_pow 5 y).div_const (5:ℝ); simpa using h
    have h7 : HasDerivAt (fun t : ℝ => t^7/7) (y^6) y := by
      have h := (hasDerivAt_pow 7 y).div_const (7:ℝ); simpa using h
    exact (((h1.sub h3).add h5).sub h7).congr_deriv (by ring)
  have hpoly : (∫ t in (0:ℝ)..x, (1 - t^2 + t^4 - t^6)) = x - x^3/3 + x^5/5 - x^7/7 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont1.intervalIntegrable 0 x)]
    norm_num
  have harctan : (∫ t in (0:ℝ)..x, (1+t^2)⁻¹) = Real.arctan x := by
    rw [integral_inv_one_add_sq]; simp
  rw [hpoly, harctan] at hmono
  linarith

/-- Alternating Taylor upper bound for `arctan` on `[0,1]`. -/
theorem arctan_taylor9_upper {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.arctan x ≤ x - x^3/3 + x^5/5 - x^7/7 + x^9/9 := by
  have hcont2 : Continuous (fun t : ℝ => 1 - t^2 + t^4 - t^6 + t^8) := by fun_prop
  have hmono : (∫ t in (0:ℝ)..x, (1+t^2)⁻¹) ≤ ∫ t in (0:ℝ)..x, (1 - t^2 + t^4 - t^6 + t^8) := by
    apply intervalIntegral.integral_mono_on hx0 (cont_inv_one_add_sq.intervalIntegrable _ _)
      (hcont2.intervalIntegrable _ _)
    intro t ht
    have ht1 : t ≤ 1 := le_trans ht.2 hx1
    rw [inv_eq_one_div, div_le_iff₀ (by positivity : (0:ℝ) < 1 + t^2)]
    have h : (1 - t^2 + t^4 - t^6 + t^8) * (1 + t^2) = 1 + t^10 := by ring
    rw [h]
    have : 0 ≤ t^10 := by positivity
    linarith
  have hderiv : ∀ y ∈ Set.uIcc (0:ℝ) x,
      HasDerivAt (fun t : ℝ => t - t^3/3 + t^5/5 - t^7/7 + t^9/9)
        (1 - y^2 + y^4 - y^6 + y^8) y := by
    intro y _
    have h1 : HasDerivAt (fun t : ℝ => t) 1 y := hasDerivAt_id y
    have h3 : HasDerivAt (fun t : ℝ => t^3/3) (y^2) y := by
      have h := (hasDerivAt_pow 3 y).div_const (3:ℝ); simpa using h
    have h5 : HasDerivAt (fun t : ℝ => t^5/5) (y^4) y := by
      have h := (hasDerivAt_pow 5 y).div_const (5:ℝ); simpa using h
    have h7 : HasDerivAt (fun t : ℝ => t^7/7) (y^6) y := by
      have h := (hasDerivAt_pow 7 y).div_const (7:ℝ); simpa using h
    have h9 : HasDerivAt (fun t : ℝ => t^9/9) (y^8) y := by
      have h := (hasDerivAt_pow 9 y).div_const (9:ℝ); simpa using h
    exact ((((h1.sub h3).add h5).sub h7).add h9).congr_deriv (by ring)
  have hpoly : (∫ t in (0:ℝ)..x, (1 - t^2 + t^4 - t^6 + t^8))
      = x - x^3/3 + x^5/5 - x^7/7 + x^9/9 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont2.intervalIntegrable 0 x)]
    norm_num
  have harctan : (∫ t in (0:ℝ)..x, (1+t^2)⁻¹) = Real.arctan x := by
    rw [integral_inv_one_add_sq]; simp
  rw [hpoly, harctan] at hmono
  linarith


/-! ### Rational constants and series bounds for the logarithms -/

noncomputable def l2lo : ℝ := 6931471803/10^10
noncomputable def l2hi : ℝ := 6931471808/10^10

lemma l2lo_le_log2 : l2lo ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  rw [l2lo]; linarith

lemma log2_le_l2hi : Real.log 2 ≤ l2hi := by
  have h := Real.log_two_lt_d9
  rw [l2hi]; linarith

/-- `log (2*(2-β)) ≤ LAf β`, a polynomial upper bound. -/
noncomputable def LAf (β : ℝ) : ℝ :=
  2*l2hi - ∑ k ∈ Finset.range 10, (β/2)^(k+1)/((k:ℝ)+1)

/-- `log (2*β) ≤ LBf β`, a polynomial upper bound. -/
noncomputable def LBf (β : ℝ) : ℝ :=
  l2hi - ∑ k ∈ Finset.range 12, (1-β)^(k+1)/((k:ℝ)+1)

theorem log_2A_le_LAf {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Real.log (2*(2-β)) ≤ LAf β := by
  have h2A : (0:ℝ) < 2*(2-β) := by linarith
  have h4 : (0:ℝ) < 4 := by norm_num
  have hpos : (0:ℝ) < 1 - β/2 := by linarith
  have h1 : (0:ℝ) < 1 - β/2 := hpos
  have hsplit : 2*(2-β) = 4*(1-β/2) := by ring
  rw [hsplit, Real.log_mul (ne_of_gt h4) (ne_of_gt hpos)]
  have hlog4 : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  rw [hlog4]
  have hlb := log_one_sub_le_neg_partial_sum 10 (y := β/2) (by positivity) (by linarith)
  have h2 := log2_le_l2hi
  rw [LAf]
  have hsum : (∑ k ∈ Finset.range 10, (β / 2) ^ (k + 1) / ((k:ℝ) + 1))
      = ∑ k ∈ Finset.range 10, (β/2)^(k+1)/((k:ℝ)+1) := rfl
  linarith [hlb, h2]

theorem log_2B_le_LBf {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Real.log (2*β) ≤ LBf β := by
  have h2B : (0:ℝ) < 2*β := by linarith
  have hsplit : 2*β = 2*(1 - (1-β)) := by ring
  have hp : (0:ℝ) < 1 - (1-β) := by linarith
  rw [hsplit, Real.log_mul (by norm_num) (ne_of_gt hp)]
  have hlb := log_one_sub_le_neg_partial_sum 12 (y := 1-β) (by linarith) (by linarith)
  have h2 := log2_le_l2hi
  rw [LBf]
  linarith [hlb, h2]


/-- `∫(1 - s²/(2S))` over `[1/4,1/2]`, with `S = (2-β)²+β²`. -/
noncomputable def J0f (β : ℝ) : ℝ :=
  1/4 - 7/(384*((2-β)^2+β^2))

/-- Upper bound for `∫(w - w²/2 + w³/3)(1-v)`, `w = s²/(4β²)`, `v = s²/(2S)`. -/
noncomputable def K2pf (β : ℝ) : ℝ :=
  7/(768*β^2) - 31/(163840*β^4) + 127/(22020096*β^6)
    - 31/(40960*β^2*((2-β)^2+β^2)) + 127/(7340032*β^4*((2-β)^2+β^2))
    - 511/(905969664*β^6*((2-β)^2+β^2))

noncomputable def stuff2f (β : ℝ) : ℝ :=
  1/4 - l2lo/(64*((2-β)^2+β^2)) - 7/(1152*((2-β)^2+β^2)) + K2pf β

/-! ### The first majorant bound -/

noncomputable def I0f (β : ℝ) : ℝ := 1/4 - 7/(768*(2-β)^2)

noncomputable def K1pf (β : ℝ) : ℝ :=
  7/(768*(2-β)^2) - 93/(163840*(2-β)^4) + 635/(44040192*(2-β)^6)
    - 511/(1811939328*(2-β)^8)

noncomputable def stuff1f (β : ℝ) : ℝ :=
  1/4 - l2lo/(128*(2-β)^2) - 7/(2304*(2-β)^2) + K1pf β

noncomputable def N1term (β : ℝ) (s : ℝ) : ℝ :=
  Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s))*(1-s^2/(4*(2-β)^2))

/-- exact value of `∫ (u - u²/2)(1-u)` with `u = s²/(4A²)`. -/
lemma intervalIntegrable_log_quarter {u : ℝ} (hu : (1/4:ℝ) ≤ u) :
    IntervalIntegrable (fun s : ℝ => Real.log s) volume (1/4) u := by
  apply ContinuousOn.intervalIntegrable
  intro s hs
  rw [Set.uIcc_of_le hu] at hs
  exact (Real.continuousAt_log (by linarith [hs.1])).continuousWithinAt

/-- `∫ (c2 s² + c4 s⁴ + c6 s⁶ + c8 s⁸)` on `[1/4,1/2]`. -/
lemma integral_poly4 (c2 c4 c6 c8 : ℝ) :
    (∫ s in (1/4:ℝ)..(1/2), c2*s^2 + c4*s^4 + c6*s^6 + c8*s^8)
      = c2*(7/192) + c4*(31/5120) + c6*(127/114688) + c8*(511/2359296) := by
  have hderiv : ∀ x ∈ Set.uIcc (1/4:ℝ) (1/2),
      HasDerivAt (fun s : ℝ => c2*(s^3/3) + c4*(s^5/5) + c6*(s^7/7) + c8*(s^9/9))
        (c2*x^2 + c4*x^4 + c6*x^6 + c8*x^8) x := by
    intro x _
    have h2 : HasDerivAt (fun s : ℝ => c2*(s^3/3)) (c2*x^2) x := by
      have h := (hasDerivAt_pow 3 x).div_const (3:ℝ)
      have := h.const_mul c2
      simpa using this
    have h4 : HasDerivAt (fun s : ℝ => c4*(s^5/5)) (c4*x^4) x := by
      have h := (hasDerivAt_pow 5 x).div_const (5:ℝ)
      have := h.const_mul c4
      simpa using this
    have h6 : HasDerivAt (fun s : ℝ => c6*(s^7/7)) (c6*x^6) x := by
      have h := (hasDerivAt_pow 7 x).div_const (7:ℝ)
      have := h.const_mul c6
      simpa using this
    have h8 : HasDerivAt (fun s : ℝ => c8*(s^9/9)) (c8*x^8) x := by
      have h := (hasDerivAt_pow 9 x).div_const (9:ℝ)
      have := h.const_mul c8
      simpa using this
    exact ((h2.add h4).add h6).add h8
  have hcont : Continuous fun s : ℝ => c2*s^2 + c4*s^4 + c6*s^6 + c8*s^8 := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  ring

lemma integral_one_sub_csq (c : ℝ) :
    (∫ s in (1/4:ℝ)..(1/2), (1:ℝ) - c*s^2) = (1/2 - 1/4) - c*(7/192) := by
  have hderiv : ∀ x ∈ Set.uIcc (1/4:ℝ) (1/2),
      HasDerivAt (fun s : ℝ => s - c*(s^3/3)) (1 - c*x^2) x := by
    intro x _
    have h2 : HasDerivAt (fun s : ℝ => c*(s^3/3)) (c*x^2) x := by
      have h := (hasDerivAt_pow 3 x).div_const (3:ℝ)
      have := h.const_mul c
      simpa using this
    exact (hasDerivAt_id x).sub h2
  have hcont : Continuous fun s : ℝ => (1:ℝ) - c*s^2 := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  ring

/-- `∫ ((-log s) + c s² log s)` on `[1/4,1/2]`. -/
lemma integral_neglog_add_sqlog (c : ℝ) :
    (∫ s in (1/4:ℝ)..(1/2), (-Real.log s) + c*(s^2*Real.log s))
      = 1/4 + c*(-(1/32)*Real.log 2 - 7/576) := by
  have h1 : IntervalIntegrable (fun s : ℝ => -Real.log s) volume (1/4) (1/2) :=
    (intervalIntegrable_log_quarter (by norm_num)).neg
  have h2 : IntervalIntegrable (fun s : ℝ => c*(s^2*Real.log s)) volume (1/4) (1/2) := by
    have h : IntervalIntegrable (fun s : ℝ => s^2*Real.log s) volume (1/4) (1/2) :=
      (intervalIntegrable_log_quarter (by norm_num)).continuousOn_mul
        (by fun_prop : ContinuousOn (fun s : ℝ => (s:ℝ)^2) (Set.uIcc (1/4) (1/2)))
    exact h.const_mul c
  rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_neg,
    intervalIntegral.integral_const_mul, integral_log_14_12, integral_sq_log_14_12]
  ring

theorem integral_N1_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∫ s in (1/4:ℝ)..(1/2), N1term β s)
      ≤ Real.log (2*(2-β)) * I0f β + stuff1f β := by
  have hA : (0:ℝ) < 2-β := by linarith
  have hA2 : (0:ℝ) < 4*(2-β)^2 := by positivity
  have h2A : (0:ℝ) < 2*(2-β) := by linarith
  have hs1 : (1/4:ℝ) ≤ 1/2 := by norm_num
  have hpt : ∀ s ∈ Set.Icc (1/4:ℝ) (1/2), N1term β s ≤
      Real.log (2*(2-β))*(1 - s^2/(4*(2-β)^2))
        + (s^2/(4*(2-β)^2) - (s^2/(4*(2-β)^2))^2/2 + (s^2/(4*(2-β)^2))^3/3)
            *(1 - s^2/(4*(2-β)^2))
        + (-Real.log s)*(1 - s^2/(4*(2-β)^2)) := by
    intro s hs
    have hs0 : (0:ℝ) < s := by linarith [hs.1]
    have hu0 : (0:ℝ) ≤ s^2/(4*(2-β)^2) := by positivity
    have hu1 : s^2/(4*(2-β)^2) ≤ 1 := by
      rw [div_le_one hA2]; nlinarith [hs.1, hs.2, sq_nonneg s]
    have hw : (0:ℝ) ≤ 1 - s^2/(4*(2-β)^2) := by linarith
    have hlog : Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s))
        = Real.log (2*(2-β)) + Real.log (1 + s^2/(4*(2-β)^2)) - Real.log s := by
      have he : (4*(2-β)^2+s^2)/(2*(2-β)*s)
          = (2*(2-β)/s) * (1 + s^2/(4*(2-β)^2)) := by
        field_simp; ring
      rw [he, Real.log_mul (by positivity) (by positivity),
        Real.log_div (by positivity) (ne_of_gt hs0)]
      ring
    have hlog2 : Real.log (1 + s^2/(4*(2-β)^2)) ≤
        s^2/(4*(2-β)^2) - (s^2/(4*(2-β)^2))^2/2 + (s^2/(4*(2-β)^2))^3/3 :=
      log_one_add_le_cubic hu0 hu1
    have hN1 : N1term β s =
        Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s))*(1 - s^2/(4*(2-β)^2)) := rfl
    rw [hN1, hlog]
    have h1 := mul_le_mul_of_nonneg_right hlog2 hw
    linarith [h1]
  have hintN : IntervalIntegrable (fun s : ℝ => N1term β s) volume (1/4) (1/2) := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    rw [Set.uIcc_of_le hs1] at hs
    have hs0 : (0:ℝ) < s := by linarith [hs.1]
    have hN1 : N1term β = fun s : ℝ =>
        Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s))*(1 - s^2/(4*(2-β)^2)) := rfl
    rw [hN1]
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · apply ContinuousAt.log
      · apply ContinuousAt.div
        · fun_prop
        · fun_prop
        · exact ne_of_gt (by positivity)
      · positivity
    · fun_prop
  have hintL : IntervalIntegrable (fun s : ℝ => Real.log s) volume (1/4) (1/2) :=
    intervalIntegrable_log_quarter (by norm_num)
  have hintR : IntervalIntegrable (fun s : ℝ =>
      Real.log (2*(2-β))*(1 - s^2/(4*(2-β)^2))
        + (s^2/(4*(2-β)^2) - (s^2/(4*(2-β)^2))^2/2 + (s^2/(4*(2-β)^2))^3/3)
            *(1 - s^2/(4*(2-β)^2))
        + (-Real.log s)*(1 - s^2/(4*(2-β)^2))) volume (1/4) (1/2) := by
    apply IntervalIntegrable.add
    · apply IntervalIntegrable.add
      · exact (by fun_prop : Continuous fun s : ℝ =>
            Real.log (2*(2-β))*(1 - s^2/(4*(2-β)^2))).intervalIntegrable _ _
      · exact (by fun_prop : Continuous fun s : ℝ =>
            (s^2/(4*(2-β)^2) - (s^2/(4*(2-β)^2))^2/2 + (s^2/(4*(2-β)^2))^3/3)
            *(1 - s^2/(4*(2-β)^2))).intervalIntegrable _ _
    · have := hintL.neg.continuousOn_mul
        (by fun_prop : ContinuousOn (fun s : ℝ => (1 - s^2/(4*(2-β)^2))) (Set.uIcc (1/4) (1/2)))
      simpa [mul_comm] using this
  have hmono := intervalIntegral.integral_mono_on hs1 hintN hintR hpt
  have hI1 : (∫ s in (1/4:ℝ)..(1/2), Real.log (2*(2-β))*(1 - s^2/(4*(2-β)^2)))
      = Real.log (2*(2-β)) * I0f β := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have he : (∫ s in (1/4:ℝ)..(1/2), (1 - s^2/(4*(2-β)^2)))
        = (∫ s in (1/4:ℝ)..(1/2), (1:ℝ) - (1/(4*(2-β)^2))*s^2) := by
      apply intervalIntegral.integral_congr; intro s _; ring
    rw [he, integral_one_sub_csq]
    rw [I0f]; field_simp
    try ring
  have hI2 : (∫ s in (1/4:ℝ)..(1/2),
        (s^2/(4*(2-β)^2) - (s^2/(4*(2-β)^2))^2/2 + (s^2/(4*(2-β)^2))^3/3)
            *(1 - s^2/(4*(2-β)^2))) = K1pf β := by
    have he : (∫ s in (1/4:ℝ)..(1/2),
        (s^2/(4*(2-β)^2) - (s^2/(4*(2-β)^2))^2/2 + (s^2/(4*(2-β)^2))^3/3)
            *(1 - s^2/(4*(2-β)^2)))
      = ∫ s in (1/4:ℝ)..(1/2), (1/(4*(2-β)^2))*s^2 + (-3/(32*(2-β)^4))*s^4
          + (5/(384*(2-β)^6))*s^6 + (-(1/(768*(2-β)^8)))*s^8 := by
      apply intervalIntegral.integral_congr
      intro s _
      have h1 : (4*(2-β)^2) ≠ 0 := by positivity
      field_simp
      ring
    rw [he, integral_poly4]
    rw [K1pf]
    field_simp
    ring
  have hI3 : (∫ s in (1/4:ℝ)..(1/2), (-Real.log s)*(1 - s^2/(4*(2-β)^2)))
      = 1/4 - Real.log 2/(128*(2-β)^2) - 7/(2304*(2-β)^2) := by
    have he : (∫ s in (1/4:ℝ)..(1/2), (-Real.log s)*(1 - s^2/(4*(2-β)^2)))
        = ∫ s in (1/4:ℝ)..(1/2), (-Real.log s) + (1/(4*(2-β)^2))*(s^2*Real.log s) := by
      apply intervalIntegral.integral_congr
      intro s _
      ring
    rw [he, integral_neglog_add_sqlog]
    field_simp
    ring
  have hsplit : (∫ s in (1/4:ℝ)..(1/2),
      Real.log (2*(2-β))*(1 - s^2/(4*(2-β)^2))
        + (s^2/(4*(2-β)^2) - (s^2/(4*(2-β)^2))^2/2 + (s^2/(4*(2-β)^2))^3/3)
            *(1 - s^2/(4*(2-β)^2))
        + (-Real.log s)*(1 - s^2/(4*(2-β)^2)))
      = (∫ s in (1/4:ℝ)..(1/2), Real.log (2*(2-β))*(1 - s^2/(4*(2-β)^2)))
        + (∫ s in (1/4:ℝ)..(1/2), (s^2/(4*(2-β)^2) - (s^2/(4*(2-β)^2))^2/2
            + (s^2/(4*(2-β)^2))^3/3)*(1 - s^2/(4*(2-β)^2)))
        + (∫ s in (1/4:ℝ)..(1/2), (-Real.log s)*(1 - s^2/(4*(2-β)^2))) := by
    have c1 : Continuous fun s : ℝ => Real.log (2*(2-β))*(1 - s^2/(4*(2-β)^2)) := by fun_prop
    have c2 : Continuous fun s : ℝ =>
        (s^2/(4*(2-β)^2) - (s^2/(4*(2-β)^2))^2/2 + (s^2/(4*(2-β)^2))^3/3)
            *(1 - s^2/(4*(2-β)^2)) := by fun_prop
    have c3 : IntervalIntegrable (fun s : ℝ => (-Real.log s)*(1 - s^2/(4*(2-β)^2)))
        volume (1/4) (1/2) := by
      have := hintL.neg.continuousOn_mul
        (by fun_prop : ContinuousOn (fun s : ℝ => (1 - s^2/(4*(2-β)^2))) (Set.uIcc (1/4) (1/2)))
      simpa [mul_comm] using this
    rw [intervalIntegral.integral_add
      (f := fun s : ℝ => Real.log (2*(2-β))*(1 - s^2/(4*(2-β)^2))
          + (s^2/(4*(2-β)^2) - (s^2/(4*(2-β)^2))^2/2 + (s^2/(4*(2-β)^2))^3/3)
              *(1 - s^2/(4*(2-β)^2)))
      (g := fun s : ℝ => (-Real.log s)*(1 - s^2/(4*(2-β)^2)))
      ((c1.add c2).intervalIntegrable _ _) c3]
    rw [intervalIntegral.integral_add (f := fun s : ℝ => Real.log (2*(2-β))*(1 - s^2/(4*(2-β)^2)))
      (g := fun s : ℝ => (s^2/(4*(2-β)^2) - (s^2/(4*(2-β)^2))^2/2 + (s^2/(4*(2-β)^2))^3/3)
              *(1 - s^2/(4*(2-β)^2)))
      (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _)]
  rw [hsplit, hI1, hI2, hI3] at hmono
  have hlog2 := l2lo_le_log2
  rw [stuff1f]
  have hpos : (0:ℝ) < 128*(2-β)^2 := by positivity
  have hkey : l2lo/(128*(2-β)^2) ≤ Real.log 2/(128*(2-β)^2) :=
    div_le_div_of_nonneg_right hlog2 hpos.le
  linarith [hmono, hkey]


theorem integral_N2_le_III {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ2 : (1/2:ℝ) ≤ β) :
    (∫ s in (1/4:ℝ)..(1/2),
        Real.log ((4*β^2+s^2)/(2*β*s))*(1 - s^2/(2*((2-β)^2+β^2))))
      ≤ Real.log (2*β) * J0f β + stuff2f β := by
  have hβp : (0:ℝ) < β := hβ0
  have hS : (0:ℝ) < (2-β)^2+β^2 := by positivity
  have hS2 : (0:ℝ) < 2*((2-β)^2+β^2) := by positivity
  have h2B : (0:ℝ) < 2*β := by linarith
  have hs1 : (1/4:ℝ) ≤ 1/2 := by norm_num
  -- pointwise bound
  have hpt : ∀ s ∈ Set.Icc (1/4:ℝ) (1/2),
      Real.log ((4*β^2+s^2)/(2*β*s))*(1 - s^2/(2*((2-β)^2+β^2))) ≤
      Real.log (2*β)*(1 - s^2/(2*((2-β)^2+β^2)))
        + (s^2/(4*β^2) - (s^2/(4*β^2))^2/2 + (s^2/(4*β^2))^3/3)
            *(1 - s^2/(2*((2-β)^2+β^2)))
        + (-Real.log s)*(1 - s^2/(2*((2-β)^2+β^2))) := by
    intro s hs
    have hs0 : (0:ℝ) < s := by linarith [hs.1]
    have hv0 : (0:ℝ) ≤ s^2/(2*((2-β)^2+β^2)) := by positivity
    have hv1 : s^2/(2*((2-β)^2+β^2)) ≤ 1 := by
      rw [div_le_one hS2]; nlinarith [hs.1, hs.2, sq_nonneg s, sq_nonneg β]
    have hw : (0:ℝ) ≤ 1 - s^2/(2*((2-β)^2+β^2)) := by linarith
    have hlog : Real.log ((4*β^2+s^2)/(2*β*s))
        = Real.log (2*β) + Real.log (1 + s^2/(4*β^2)) - Real.log s := by
      have he : (4*β^2+s^2)/(2*β*s) = (2*β/s) * (1 + s^2/(4*β^2)) := by
        field_simp; ring
      rw [he, Real.log_mul (by positivity) (by positivity),
        Real.log_div (by positivity) (ne_of_gt hs0)]
      ring
    have hlog2 : Real.log (1 + s^2/(4*β^2)) ≤
        s^2/(4*β^2) - (s^2/(4*β^2))^2/2 + (s^2/(4*β^2))^3/3 := by
      apply log_one_add_le_cubic (by positivity)
      rw [div_le_one (by positivity)]; nlinarith [hs.1, hs.2, sq_nonneg s, sq_nonneg β, hβp]
    rw [hlog]
    have h1 := mul_le_mul_of_nonneg_right hlog2 hw
    linarith [h1]
  have hintN : IntervalIntegrable (fun s : ℝ =>
      Real.log ((4*β^2+s^2)/(2*β*s))*(1 - s^2/(2*((2-β)^2+β^2)))) volume (1/4) (1/2) := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    rw [Set.uIcc_of_le hs1] at hs
    have hs0 : (0:ℝ) < s := by linarith [hs.1]
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · apply ContinuousAt.log
      · apply ContinuousAt.div
        · fun_prop
        · fun_prop
        · have : (0:ℝ) < 2*β*s := by positivity
          exact ne_of_gt this
      · positivity
    · fun_prop
  have hintL : IntervalIntegrable (fun s : ℝ => Real.log s) volume (1/4) (1/2) :=
    intervalIntegrable_log_quarter (by norm_num)
  have hintR : IntervalIntegrable (fun s : ℝ =>
      Real.log (2*β)*(1 - s^2/(2*((2-β)^2+β^2)))
        + (s^2/(4*β^2) - (s^2/(4*β^2))^2/2 + (s^2/(4*β^2))^3/3)
            *(1 - s^2/(2*((2-β)^2+β^2)))
        + (-Real.log s)*(1 - s^2/(2*((2-β)^2+β^2)))) volume (1/4) (1/2) := by
    apply IntervalIntegrable.add
    · apply IntervalIntegrable.add
      · exact (by fun_prop : Continuous fun s : ℝ =>
            Real.log (2*β)*(1 - s^2/(2*((2-β)^2+β^2)))).intervalIntegrable _ _
      · exact (by fun_prop : Continuous fun s : ℝ =>
            (s^2/(4*β^2) - (s^2/(4*β^2))^2/2 + (s^2/(4*β^2))^3/3)
            *(1 - s^2/(2*((2-β)^2+β^2)))).intervalIntegrable _ _
    · have := hintL.neg.continuousOn_mul
        (by fun_prop : ContinuousOn (fun s : ℝ => (1 - s^2/(2*((2-β)^2+β^2))))
          (Set.uIcc (1/4) (1/2)))
      simpa [mul_comm] using this
  have hmono := intervalIntegral.integral_mono_on hs1 hintN hintR hpt
  have hI1 : (∫ s in (1/4:ℝ)..(1/2), Real.log (2*β)*(1 - s^2/(2*((2-β)^2+β^2))))
      = Real.log (2*β) * J0f β := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have he : (∫ s in (1/4:ℝ)..(1/2), (1 - s^2/(2*((2-β)^2+β^2))))
        = (∫ s in (1/4:ℝ)..(1/2), (1:ℝ) - (1/(2*((2-β)^2+β^2)))*s^2) := by
      apply intervalIntegral.integral_congr; intro s _; ring
    rw [he, integral_one_sub_csq]
    rw [J0f]; field_simp
    try ring
  have hI2 : (∫ s in (1/4:ℝ)..(1/2),
        (s^2/(4*β^2) - (s^2/(4*β^2))^2/2 + (s^2/(4*β^2))^3/3)
            *(1 - s^2/(2*((2-β)^2+β^2)))) = K2pf β := by
    have he : (∫ s in (1/4:ℝ)..(1/2),
        (s^2/(4*β^2) - (s^2/(4*β^2))^2/2 + (s^2/(4*β^2))^3/3)
            *(1 - s^2/(2*((2-β)^2+β^2))))
      = ∫ s in (1/4:ℝ)..(1/2), (1/(4*β^2))*s^2
          + (-(1/(32*β^4)) - 1/(8*β^2*((2-β)^2+β^2)))*s^4
          + (1/(192*β^6) + 1/(64*β^4*((2-β)^2+β^2)))*s^6
          + (-(1/(384*β^6*((2-β)^2+β^2))))*s^8 := by
      apply intervalIntegral.integral_congr
      intro s _
      have h1 : (4*β^2) ≠ 0 := by positivity
      have h2 : (2*((2-β)^2+β^2)) ≠ 0 := by positivity
      field_simp
      ring
    rw [he, integral_poly4]
    rw [K2pf]
    have h1 : (β) ≠ 0 := ne_of_gt hβp
    have h2 : (2-β)^2+β^2 ≠ 0 := ne_of_gt hS
    field_simp
    ring
  have hI3 : (∫ s in (1/4:ℝ)..(1/2), (-Real.log s)*(1 - s^2/(2*((2-β)^2+β^2))))
      = 1/4 - Real.log 2/(64*((2-β)^2+β^2)) - 7/(1152*((2-β)^2+β^2)) := by
    have he : (∫ s in (1/4:ℝ)..(1/2), (-Real.log s)*(1 - s^2/(2*((2-β)^2+β^2))))
        = ∫ s in (1/4:ℝ)..(1/2), (-Real.log s)
            + (1/(2*((2-β)^2+β^2)))*(s^2*Real.log s) := by
      apply intervalIntegral.integral_congr
      intro s _
      ring
    rw [he, integral_neglog_add_sqlog]
    field_simp
    ring
  have hsplit : (∫ s in (1/4:ℝ)..(1/2),
      Real.log (2*β)*(1 - s^2/(2*((2-β)^2+β^2)))
        + (s^2/(4*β^2) - (s^2/(4*β^2))^2/2 + (s^2/(4*β^2))^3/3)
            *(1 - s^2/(2*((2-β)^2+β^2)))
        + (-Real.log s)*(1 - s^2/(2*((2-β)^2+β^2))))
      = (∫ s in (1/4:ℝ)..(1/2), Real.log (2*β)*(1 - s^2/(2*((2-β)^2+β^2))))
        + (∫ s in (1/4:ℝ)..(1/2), (s^2/(4*β^2) - (s^2/(4*β^2))^2/2
            + (s^2/(4*β^2))^3/3)*(1 - s^2/(2*((2-β)^2+β^2))))
        + (∫ s in (1/4:ℝ)..(1/2), (-Real.log s)*(1 - s^2/(2*((2-β)^2+β^2)))) := by
    have c1 : Continuous fun s : ℝ => Real.log (2*β)*(1 - s^2/(2*((2-β)^2+β^2))) := by fun_prop
    have c2 : Continuous fun s : ℝ =>
        (s^2/(4*β^2) - (s^2/(4*β^2))^2/2 + (s^2/(4*β^2))^3/3)
            *(1 - s^2/(2*((2-β)^2+β^2))) := by fun_prop
    have c3 : IntervalIntegrable (fun s : ℝ => (-Real.log s)*(1 - s^2/(2*((2-β)^2+β^2))))
        volume (1/4) (1/2) := by
      have := hintL.neg.continuousOn_mul
        (by fun_prop : ContinuousOn (fun s : ℝ => (1 - s^2/(2*((2-β)^2+β^2))))
          (Set.uIcc (1/4) (1/2)))
      simpa [mul_comm] using this
    rw [intervalIntegral.integral_add
      (f := fun s : ℝ => Real.log (2*β)*(1 - s^2/(2*((2-β)^2+β^2)))
          + (s^2/(4*β^2) - (s^2/(4*β^2))^2/2 + (s^2/(4*β^2))^3/3)
              *(1 - s^2/(2*((2-β)^2+β^2))))
      (g := fun s : ℝ => (-Real.log s)*(1 - s^2/(2*((2-β)^2+β^2))))
      ((c1.add c2).intervalIntegrable _ _) c3]
    rw [intervalIntegral.integral_add (f := fun s : ℝ => Real.log (2*β)*(1 - s^2/(2*((2-β)^2+β^2))))
      (g := fun s : ℝ => (s^2/(4*β^2) - (s^2/(4*β^2))^2/2 + (s^2/(4*β^2))^3/3)
              *(1 - s^2/(2*((2-β)^2+β^2))))
      (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _)]
  rw [hsplit, hI1, hI2, hI3] at hmono
  have hlog2 := l2lo_le_log2
  rw [stuff2f]
  have hpos : (0:ℝ) < 64*((2-β)^2+β^2) := by positivity
  have hkey : l2lo/(64*((2-β)^2+β^2)) ≤ Real.log 2/(64*((2-β)^2+β^2)) :=
    div_le_div_of_nonneg_right hlog2 hpos.le
  linarith [hmono, hkey]


section Psi
noncomputable def psi7 (x : ℝ) : ℝ := x - x^3/3 + x^5/5 - x^7/7

lemma psi7_le_arctan {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : psi7 x ≤ Real.arctan x := by
  rw [psi7]; exact arctan_taylor7_lower hx0 hx1
end Psi


lemma dl1_bound {β : ℝ} (hβ1 : β < 1) : 0 < dl1 β ∧ dl1 β ≤ 1 := by
  constructor
  · rw [dl1]; apply div_pos <;> nlinarith [sq_nonneg (β - 3/2)]
  · rw [dl1]
    rw [div_le_one (by nlinarith [sq_nonneg (β - 3/2)])]
    nlinarith [sq_nonneg (β - 11/8)]

lemma dl2_bound {β : ℝ} (hβ0 : 0 < β) : 0 < dl2 β ∧ dl2 β ≤ 1 := by
  constructor
  · rw [dl2]; apply div_pos <;> nlinarith [sq_nonneg (1+β)]
  · rw [dl2]
    rw [div_le_one (by nlinarith [sq_nonneg (1+β)])]
    nlinarith [sq_nonneg (1+β)]

lemma dlr_bound {β : ℝ} (hβ1 : β < 1) : 0 < dlr β ∧ dlr β ≤ 1 := by
  constructor
  · rw [dlr]; apply div_pos <;> nlinarith [sq_nonneg (2-β)]
  · rw [dlr]
    rw [div_le_one (by nlinarith [sq_nonneg (2-β)])]
    nlinarith [sq_nonneg (2-β)]

/-- The final polynomial surrogate bounding the integral from below (region III). -/
noncomputable def FF (β : ℝ) : ℝ :=
  (13/5)*(psi7 (dl1 β) + psi7 (dl2 β)) + Ctot β * psi7 (dlr β) + P4r β + P5r β
    - LAf β * I0f β - stuff1f β - LBf β * J0f β - stuff2f β


/-- The intermediate surrogate: `∫ ≥ Fint β` (region III). -/
noncomputable def Fint (β : ℝ) : ℝ :=
  (13/5)*(FA β + FB β) + Ctot β * FD β + P4r β + P5r β
    - Real.log (2*(2-β)) * I0f β - stuff1f β - Real.log (2*β) * J0f β - stuff2f β

theorem integral_ge_Fint {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ2 : (1/2:ℝ) ≤ β) :
    Fint β ≤ ∫ s in (1/4:ℝ)..(1/2),
      (Tterm β s - N1term β s
        - Real.log ((4*β^2+s^2)/(2*β*s))*(1 - s^2/(2*((2-β)^2+β^2)))) := by
  have hs1 : (1/4:ℝ) ≤ 1/2 := by norm_num
  have hT := integral_T_term hβ0 hβ1
  have hN1 := integral_N1_le hβ0 hβ1
  have hN2 := integral_N2_le_III hβ0 hβ1 hβ2
  -- integrability
  have hcT : IntervalIntegrable (fun s : ℝ => Tterm β s) volume (1/4) (1/2) := by
    have hA : (0:ℝ) < 2-β := by linarith
    have h1 : (0:ℝ) < 3/2-β := by linarith
    have h2 : (0:ℝ) < 1+β := by linarith
    have hcA : Continuous fun s : ℝ => ((3/2-β) : ℝ)/((3/2-β)^2+s^2) :=
      (continuous_const (y := ((3/2-β):ℝ))).div (by fun_prop) (by intro s; positivity)
    have hcB : Continuous fun s : ℝ => ((1+β) : ℝ)/((1+β)^2+s^2) :=
      (continuous_const (y := ((1+β):ℝ))).div (by fun_prop) (by intro s; positivity)
    have hcAB : Continuous fun s : ℝ => (13/5)*(((3/2-β)/((3/2-β)^2+s^2))+((1+β)/((1+β)^2+s^2))) :=
      Continuous.const_mul (hcA.add hcB) _
    have hc1 : Continuous fun s : ℝ => (((2-β)^2-β^2) : ℝ)/(2*((2-β)^2+s^2)) :=
      (continuous_const (y := ((2-β)^2-β^2 : ℝ))).div (by fun_prop) (by intro s; positivity)
    have hc2 : Continuous fun s : ℝ => (((2-β)^2-β^2)^2 : ℝ)/(8*((2-β)^2+s^2)^2) :=
      (continuous_const (y := (((2-β)^2-β^2)^2 : ℝ))).div (by fun_prop) (by intro s; positivity)
    have hc3 : Continuous fun s : ℝ => (((2-β)^2-β^2)^3 : ℝ)/(16*((2-β)^2+s^2)^3) :=
      (continuous_const (y := (((2-β)^2-β^2)^3 : ℝ))).div (by fun_prop) (by intro s; positivity)
    have hc : Continuous (fun s : ℝ => Tterm β s) := by
      unfold Tterm
      exact ((hcAB.add hc1).add hc2).add hc3
    exact hc.intervalIntegrable _ _
  have hcN1 : IntervalIntegrable (fun s : ℝ => N1term β s) volume (1/4) (1/2) := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    rw [Set.uIcc_of_le hs1] at hs
    have hs0 : (0:ℝ) < s := by linarith [hs.1]
    have hAb : (0:ℝ) < 2-β := by linarith
    have hN1 : N1term β = fun s : ℝ =>
        Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s))*(1 - s^2/(4*(2-β)^2)) := rfl
    rw [hN1]
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · apply ContinuousAt.log
      · apply ContinuousAt.div
        · fun_prop
        · fun_prop
        · exact ne_of_gt (by positivity : (0:ℝ) < 2*(2-β)*s)
      · positivity
    · fun_prop
  have hcN2 : IntervalIntegrable (fun s : ℝ =>
      Real.log ((4*β^2+s^2)/(2*β*s))*(1 - s^2/(2*((2-β)^2+β^2)))) volume (1/4) (1/2) := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    rw [Set.uIcc_of_le hs1] at hs
    have hs0 : (0:ℝ) < s := by linarith [hs.1]
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · apply ContinuousAt.log
      · apply ContinuousAt.div
        · fun_prop
        · fun_prop
        · exact ne_of_gt (by positivity : (0:ℝ) < 2*β*s)
      · positivity
    · fun_prop
  have hsplit : (∫ s in (1/4:ℝ)..(1/2),
      (Tterm β s - N1term β s
        - Real.log ((4*β^2+s^2)/(2*β*s))*(1 - s^2/(2*((2-β)^2+β^2)))))
      = (∫ s in (1/4:ℝ)..(1/2), Tterm β s) - (∫ s in (1/4:ℝ)..(1/2), N1term β s)
        - (∫ s in (1/4:ℝ)..(1/2),
            Real.log ((4*β^2+s^2)/(2*β*s))*(1 - s^2/(2*((2-β)^2+β^2)))) := by
    rw [intervalIntegral.integral_sub (hcT.sub hcN1) hcN2,
      intervalIntegral.integral_sub hcT hcN1]
  rw [hsplit, hT]
  have h1 : psi7 (dl1 β) ≤ FA β := by
    rw [FA_eq_arctan hβ0 hβ1]
    obtain ⟨ha, hb⟩ := dl1_bound hβ1
    exact psi7_le_arctan ha.le hb
  have h2 : psi7 (dl2 β) ≤ FB β := by
    rw [FB_eq_arctan hβ0 hβ1]
    obtain ⟨ha, hb⟩ := dl2_bound hβ0
    exact psi7_le_arctan ha.le hb
  have h3 : psi7 (dlr β) ≤ FD β := by
    rw [FD_eq_arctan hβ0 hβ1]
    obtain ⟨ha, hb⟩ := dlr_bound hβ1
    exact psi7_le_arctan ha.le hb
  have hCt0 : 0 ≤ Ctot β := by
    rw [Ctot]
    have hd : (0:ℝ) ≤ (2-β)^2-β^2 := by nlinarith
    have hA : (0:ℝ) < 2-β := by linarith
    have : (0:ℝ) ≤ 4*(1-β) := by linarith
    have he : (2-β)^2-β^2 = 4*(1-β) := by ring
    rw [he]
    positivity
  have hI1 := integral_N1_le hβ0 hβ1
  have hI2 := integral_N2_le_III hβ0 hβ1 hβ2
  have hlA := log_2A_le_LAf hβ0 hβ1
  have hlB := log_2B_le_LBf hβ0 hβ1
  have hI0 : 0 ≤ I0f β := by
    rw [I0f]
    have h1 : 7/(768*(2-β)^2) ≤ 7/768 :=
      div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 7) (by norm_num : (0:ℝ) < 768)
        (by nlinarith [sq_nonneg (2-β), hβ1])
    linarith
  have hJ0 : 0 ≤ J0f β := by
    rw [J0f]
    have hS : (2:ℝ) ≤ (2-β)^2+β^2 := by nlinarith [sq_nonneg (2-β), sq_nonneg β, hβ0, hβ1]
    have h1 : (768:ℝ) ≤ 384*((2-β)^2+β^2) := by linarith
    have h2 : 7/(384*((2-β)^2+β^2)) ≤ 7/768 :=
      div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 7) (by norm_num : (0:ℝ) < 768) h1
    linarith
  have hmul1 : Real.log (2*(2-β)) * I0f β ≤ LAf β * I0f β :=
    mul_le_mul_of_nonneg_right hlA hI0
  have hmul2 : Real.log (2*β) * J0f β ≤ LBf β * J0f β :=
    mul_le_mul_of_nonneg_right hlB hJ0
  have hmul3 : Ctot β * psi7 (dlr β) ≤ Ctot β * FD β := mul_le_mul_of_nonneg_left h3 hCt0
  have h5 : (13/5)*psi7 (dl1 β) + (13/5)*psi7 (dl2 β) ≤ (13/5)*(FA β + FB β) := by
    have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 13/5)
    have := mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 13/5)
    linarith
  rw [Fint]
  linarith [h5, hmul3, hmul1, hmul2, hI1, hI2]

theorem FF_le_Fint {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ2 : (1/2:ℝ) ≤ β) :
    FF β ≤ Fint β := by
  have h1 : psi7 (dl1 β) ≤ FA β := by
    rw [FA_eq_arctan hβ0 hβ1]
    obtain ⟨ha, hb⟩ := dl1_bound hβ1
    exact psi7_le_arctan ha.le hb
  have h2 : psi7 (dl2 β) ≤ FB β := by
    rw [FB_eq_arctan hβ0 hβ1]
    obtain ⟨ha, hb⟩ := dl2_bound hβ0
    exact psi7_le_arctan ha.le hb
  have h3 : psi7 (dlr β) ≤ FD β := by
    rw [FD_eq_arctan hβ0 hβ1]
    obtain ⟨ha, hb⟩ := dlr_bound hβ1
    exact psi7_le_arctan ha.le hb
  have hCt0 : 0 ≤ Ctot β := by
    rw [Ctot]
    have he : (2-β)^2-β^2 = 4*(1-β) := by ring
    rw [he]
    have hA : (0:ℝ) < 2-β := by linarith
    have h4 : (0:ℝ) ≤ 4*(1-β) := by linarith
    have h3 : (0:ℝ) < 2-β := hA
    positivity
  have hI0 : 0 ≤ I0f β := by
    rw [I0f]
    have h1 : 7/(768*(2-β)^2) ≤ 7/768 :=
      div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 7) (by norm_num : (0:ℝ) < 768)
        (by nlinarith [sq_nonneg (2-β), hβ1])
    linarith
  have hJ0 : 0 ≤ J0f β := by
    rw [J0f]
    have hS : (2:ℝ) ≤ (2-β)^2+β^2 := by nlinarith [sq_nonneg (2-β), sq_nonneg β, hβ0, hβ1]
    have h1 : (768:ℝ) ≤ 384*((2-β)^2+β^2) := by linarith
    have h2 : 7/(384*((2-β)^2+β^2)) ≤ 7/768 :=
      div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 7) (by norm_num : (0:ℝ) < 768) h1
    linarith
  have hmul1 : Real.log (2*(2-β)) * I0f β ≤ LAf β * I0f β :=
    mul_le_mul_of_nonneg_right (log_2A_le_LAf hβ0 hβ1) hI0
  have hmul2 : Real.log (2*β) * J0f β ≤ LBf β * J0f β :=
    mul_le_mul_of_nonneg_right (log_2B_le_LBf hβ0 hβ1) hJ0
  have hmul3 : Ctot β * psi7 (dlr β) ≤ Ctot β * FD β := mul_le_mul_of_nonneg_left h3 hCt0
  have h5 : (13/5)*psi7 (dl1 β) + (13/5)*psi7 (dl2 β) ≤ (13/5)*(FA β + FB β) := by
    have h1' := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 13/5)
    have h2' := mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 13/5)
    linarith
  rw [FF, Fint]
  linarith [h5, hmul3, hmul1, hmul2]

theorem integral_ge_FF {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ2 : (1/2:ℝ) ≤ β) :
    FF β ≤ ∫ s in (1/4:ℝ)..(1/2),
      (Tterm β s - N1term β s
        - Real.log ((4*β^2+s^2)/(2*β*s))*(1 - s^2/(2*((2-β)^2+β^2)))) :=
  le_trans (FF_le_Fint hβ0 hβ1 hβ2) (integral_ge_Fint hβ0 hβ1 hβ2)

/-! ## The target statement -/


/-! ## Helper development (derivatives, bounds, chord assembly) -/


set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1000000

/-! ### Polynomial derivative helpers -/

lemma hasDerivAt_lin (c0 c1 : ℝ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => c1*t + c0) (c1) x := by
  have hh := (Polynomial.C c1 * Polynomial.X + Polynomial.C c0 : Polynomial ℝ).hasDerivAt x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero, Polynomial.eval_one, Polynomial.eval_neg,
    Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X, Polynomial.derivative_neg,
    mul_one, mul_zero, add_zero, zero_add, sub_zero, one_mul, zero_mul, neg_zero] at hh
  exact hh.congr_deriv (by ring)

lemma hasDerivAt_quad (c0 c1 c2 : ℝ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => c2*t^2 + c1*t + c0) (2*c2*x + c1) x := by
  have hh := (Polynomial.C c2 * Polynomial.X^2 + Polynomial.C c1 * Polynomial.X + Polynomial.C c0 : Polynomial ℝ).hasDerivAt x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero, Polynomial.eval_one, Polynomial.eval_neg,
    Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X, Polynomial.derivative_neg,
    mul_one, mul_zero, add_zero, zero_add, sub_zero, one_mul, zero_mul, neg_zero] at hh
  exact hh.congr_deriv (by ring)

lemma hasDerivAt_cubic (c0 c1 c2 c3 : ℝ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => c3*t^3 + c2*t^2 + c1*t + c0) (3*c3*x^2 + 2*c2*x + c1) x := by
  have hh := (Polynomial.C c3 * Polynomial.X^3 + Polynomial.C c2 * Polynomial.X^2 + Polynomial.C c1 * Polynomial.X + Polynomial.C c0 : Polynomial ℝ).hasDerivAt x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero, Polynomial.eval_one, Polynomial.eval_neg,
    Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X, Polynomial.derivative_neg,
    mul_one, mul_zero, add_zero, zero_add, sub_zero, one_mul, zero_mul, neg_zero] at hh
  exact hh.congr_deriv (by ring)

lemma hasDerivAt_quart (c0 c1 c2 c3 c4 : ℝ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => c4*t^4 + c3*t^3 + c2*t^2 + c1*t + c0) (4*c4*x^3 + 3*c3*x^2 + 2*c2*x + c1) x := by
  have hh := (Polynomial.C c4 * Polynomial.X^4 + Polynomial.C c3 * Polynomial.X^3 + Polynomial.C c2 * Polynomial.X^2 + Polynomial.C c1 * Polynomial.X + Polynomial.C c0 : Polynomial ℝ).hasDerivAt x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero, Polynomial.eval_one, Polynomial.eval_neg,
    Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X, Polynomial.derivative_neg,
    mul_one, mul_zero, add_zero, zero_add, sub_zero, one_mul, zero_mul, neg_zero] at hh
  exact hh.congr_deriv (by ring)

lemma hasDerivAt_quint (c0 c1 c2 c3 c4 c5 : ℝ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => c5*t^5 + c4*t^4 + c3*t^3 + c2*t^2 + c1*t + c0) (5*c5*x^4 + 4*c4*x^3 + 3*c3*x^2 + 2*c2*x + c1) x := by
  have hh := (Polynomial.C c5 * Polynomial.X^5 + Polynomial.C c4 * Polynomial.X^4 + Polynomial.C c3 * Polynomial.X^3 + Polynomial.C c2 * Polynomial.X^2 + Polynomial.C c1 * Polynomial.X + Polynomial.C c0 : Polynomial ℝ).hasDerivAt x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero, Polynomial.eval_one, Polynomial.eval_neg,
    Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X, Polynomial.derivative_neg,
    mul_one, mul_zero, add_zero, zero_add, sub_zero, one_mul, zero_mul, neg_zero] at hh
  exact hh.congr_deriv (by ring)

lemma hasDerivAt_sext (c0 c1 c2 c3 c4 c5 c6 : ℝ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => c6*t^6 + c5*t^5 + c4*t^4 + c3*t^3 + c2*t^2 + c1*t + c0) (6*c6*x^5 + 5*c5*x^4 + 4*c4*x^3 + 3*c3*x^2 + 2*c2*x + c1) x := by
  have hh := (Polynomial.C c6 * Polynomial.X^6 + Polynomial.C c5 * Polynomial.X^5 + Polynomial.C c4 * Polynomial.X^4 + Polynomial.C c3 * Polynomial.X^3 + Polynomial.C c2 * Polynomial.X^2 + Polynomial.C c1 * Polynomial.X + Polynomial.C c0 : Polynomial ℝ).hasDerivAt x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero, Polynomial.eval_one, Polynomial.eval_neg,
    Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X, Polynomial.derivative_neg,
    mul_one, mul_zero, add_zero, zero_add, sub_zero, one_mul, zero_mul, neg_zero] at hh
  exact hh.congr_deriv (by ring)

lemma hasDerivAt_sept (c0 c1 c2 c3 c4 c5 c6 c7 : ℝ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => c7*t^7 + c6*t^6 + c5*t^5 + c4*t^4 + c3*t^3 + c2*t^2 + c1*t + c0) (7*c7*x^6 + 6*c6*x^5 + 5*c5*x^4 + 4*c4*x^3 + 3*c3*x^2 + 2*c2*x + c1) x := by
  have hh := (Polynomial.C c7 * Polynomial.X^7 + Polynomial.C c6 * Polynomial.X^6 + Polynomial.C c5 * Polynomial.X^5 + Polynomial.C c4 * Polynomial.X^4 + Polynomial.C c3 * Polynomial.X^3 + Polynomial.C c2 * Polynomial.X^2 + Polynomial.C c1 * Polynomial.X + Polynomial.C c0 : Polynomial ℝ).hasDerivAt x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero, Polynomial.eval_one, Polynomial.eval_neg,
    Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X, Polynomial.derivative_neg,
    mul_one, mul_zero, add_zero, zero_add, sub_zero, one_mul, zero_mul, neg_zero] at hh
  exact hh.congr_deriv (by ring)

lemma hasDerivAt_oct (c0 c1 c2 c3 c4 c5 c6 c7 c8 : ℝ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => c8*t^8 + c7*t^7 + c6*t^6 + c5*t^5 + c4*t^4 + c3*t^3 + c2*t^2 + c1*t + c0) (8*c8*x^7 + 7*c7*x^6 + 6*c6*x^5 + 5*c5*x^4 + 4*c4*x^3 + 3*c3*x^2 + 2*c2*x + c1) x := by
  have hh := (Polynomial.C c8 * Polynomial.X^8 + Polynomial.C c7 * Polynomial.X^7 + Polynomial.C c6 * Polynomial.X^6 + Polynomial.C c5 * Polynomial.X^5 + Polynomial.C c4 * Polynomial.X^4 + Polynomial.C c3 * Polynomial.X^3 + Polynomial.C c2 * Polynomial.X^2 + Polynomial.C c1 * Polynomial.X + Polynomial.C c0 : Polynomial ℝ).hasDerivAt x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero, Polynomial.eval_one, Polynomial.eval_neg,
    Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X, Polynomial.derivative_neg,
    mul_one, mul_zero, add_zero, zero_add, sub_zero, one_mul, zero_mul, neg_zero] at hh
  exact hh.congr_deriv (by ring)


/-! ### Derivatives of `psi7` -/

noncomputable def dpsi7 (x : ℝ) : ℝ := 1 - x^2 + x^4 - x^6
noncomputable def d2psi7 (x : ℝ) : ℝ := -2*x + 4*x^3 - 6*x^5

lemma hasDerivAt_psi7 (x : ℝ) : HasDerivAt psi7 (dpsi7 x) x := by
  have h1 : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  have h3 : HasDerivAt (fun t : ℝ => t^3/3) (3*x^2/3) x := by
    have h : HasDerivAt (fun t : ℝ => t^3) (3*x^2) x := by simpa using hasDerivAt_pow 3 x
    exact h.div_const 3
  have h5 : HasDerivAt (fun t : ℝ => t^5/5) (5*x^4/5) x := by
    have h : HasDerivAt (fun t : ℝ => t^5) (5*x^4) x := by simpa using hasDerivAt_pow 5 x
    exact h.div_const 5
  have h7 : HasDerivAt (fun t : ℝ => t^7/7) (7*x^6/7) x := by
    have h : HasDerivAt (fun t : ℝ => t^7) (7*x^6) x := by simpa using hasDerivAt_pow 7 x
    exact h.div_const 7
  have hcomb := (((h1.sub h3).add h5).sub h7)
  unfold psi7
  refine hcomb.congr_deriv ?_
  simp only [dpsi7]; ring

lemma hasDerivAt_dpsi7 (x : ℝ) : HasDerivAt dpsi7 (d2psi7 x) x := by
  have h0 : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 x := hasDerivAt_const x 1
  have h2 : HasDerivAt (fun t : ℝ => t^2) (2*x) x := by simpa using hasDerivAt_pow 2 x
  have h4 : HasDerivAt (fun t : ℝ => t^4) (4*x^3) x := by simpa using hasDerivAt_pow 4 x
  have h6 : HasDerivAt (fun t : ℝ => t^6) (6*x^5) x := by simpa using hasDerivAt_pow 6 x
  have hcomb := (((h0.sub h2).add h4).sub h6)
  unfold dpsi7
  refine hcomb.congr_deriv ?_
  simp only [d2psi7]; ring

lemma dpsi7_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ dpsi7 x := by
  have h : dpsi7 x = 1 - x^2*(1 - x^2 + x^4) := by simp only [dpsi7]; ring
  rw [h]
  have hx2 : x^2 ≤ 1 := by nlinarith
  have hfac : (0:ℝ) ≤ 1 - x^2 + x^4 := by nlinarith [sq_nonneg (x^2 - 1/2)]
  have hfac2 : 1 - x^2 + x^4 ≤ 1 := by nlinarith [sq_nonneg x]
  have h1 : x^2*(1 - x^2 + x^4) ≤ 1 := by
    simpa using mul_le_mul hx2 hfac2 hfac (by norm_num : (0:ℝ) ≤ 1)
  linarith

lemma dpsi7_le_one (x : ℝ) : dpsi7 x ≤ 1 := by
  have h : dpsi7 x = 1 - x^2*(1 - x^2 + x^4) := by simp only [dpsi7]; ring
  rw [h]
  nlinarith [sq_nonneg x, sq_nonneg (x^2 - 1/2)]

lemma d2psi7_nonpos {x : ℝ} (hx0 : 0 ≤ x) : d2psi7 x ≤ 0 := by
  have h : d2psi7 x = -2*x*(1 - 2*x^2 + 3*x^4) := by simp only [d2psi7]; ring
  rw [h]
  have h1 : 0 ≤ 1 - 2*x^2 + 3*x^4 := by nlinarith [sq_nonneg (3*x^2-1)]
  nlinarith

/-! ### Derivatives of `dl1` -/

noncomputable def dd1 (b : ℝ) : ℝ := 2*(8*b^2-24*b+17)/(8*b^2-24*b+19)^2
noncomputable def d2d1 (b : ℝ) : ℝ := 2*(16*b-24)*(4-(8*b^2-24*b+19))/(8*b^2-24*b+19)^3

/-- `d/db (3 - 2b) = -2`. -/
lemma hd_lin3 (b : ℝ) : HasDerivAt (fun t : ℝ => 3-2*t) (-2) b := by
  have hfun : (fun t : ℝ => 3-2*t) = (fun t : ℝ => (-2)*t + 3) := by funext t; ring
  rw [hfun]
  exact (hasDerivAt_lin (3:ℝ) (-2) b).congr_deriv (by ring)

/-- `d/db (8b² - 24b + 19) = 16b - 24`. -/
lemma hd_q1 (b : ℝ) : HasDerivAt (fun t : ℝ => 8*t^2-24*t+19) (16*b-24) b := by
  have hh := hasDerivAt_quad (19:ℝ) (-24) 8 b
  convert hh using 1 <;> (first | (ext t; ring) | ring)

/-- `d/db (16b² - 48b + 34) = 32b - 48`. -/
lemma hd_q2 (b : ℝ) : HasDerivAt (fun t : ℝ => 2*(8*t^2-24*t+17)) (2*(16*b-24)) b := by
  have hh := hasDerivAt_quad (34:ℝ) (-48) 16 b
  convert hh using 1 <;> (first | (ext t; ring) | ring)

/-- `d/db ((8b² - 24b + 19)²)`. -/
lemma hd_q1sq (b : ℝ) : HasDerivAt (fun t : ℝ => (8*t^2-24*t+19)^2)
    (2*(8*b^2-24*b+19)*(16*b-24)) b := by
  have hh := hasDerivAt_quart (361:ℝ) (-912) 880 (-384) 64 b
  convert hh using 1 <;> (first | (ext t; ring) | ring)

lemma hasDerivAt_dl1 (b : ℝ) (h : (8*b^2-24*b+19) ≠ 0) : HasDerivAt dl1 (dd1 b) b := by
  have hdiv := (hd_lin3 b).div (hd_q1 b) h
  unfold dl1
  have hfun : (fun t : ℝ => (3-2*t)/(8*t^2-24*t+19)) = (fun t : ℝ => 3-2*t) / (fun t : ℝ => 8*t^2-24*t+19) := rfl
  rw [hfun]
  refine hdiv.congr_deriv ?_
  simp only [dd1]
  field_simp
  ring

lemma hasDerivAt_dd1 (b : ℝ) (h : (8*b^2-24*b+19) ≠ 0) : HasDerivAt dd1 (d2d1 b) b := by
  have hdiv := (hd_q2 b).div (hd_q1sq b) (pow_ne_zero 2 h)
  unfold dd1
  have hfun : (fun t : ℝ => 2*(8*t^2-24*t+17)/(8*t^2-24*t+19)^2)
      = (fun t : ℝ => 2*(8*t^2-24*t+17)) / (fun t : ℝ => (8*t^2-24*t+19)^2) := rfl
  rw [hfun]
  refine hdiv.congr_deriv ?_
  simp only [dd1, d2d1]
  field_simp
  ring

lemma d2d1_le {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : d2d1 b ≤ 1/2 := by
  have hid : d2d1 b
      = (-16+96*(1-b)+384*(1-b)^2+256*(1-b)^3)/(3+8*(1-b)+8*(1-b)^2)^3 := by
    simp only [d2d1]; ring
  rw [hid]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (3+8*(1-b)+8*(1-b)^2)^3)]
  have hcert : (0:ℝ) ≤ (1/2)*(3+8*(1-b)+8*(1-b)^2)^3
      - (-16+96*(1-b)+384*(1-b)^2+256*(1-b)^3) := by
    have hh : (1/2)*(3+8*(1-b)+8*(1-b)^2)^3 - (-16+96*(1-b)+384*(1-b)^2+256*(1-b)^3)
        = (59/2:ℝ) + 12*(1-b) + 12*(1-b)^2 + 576*(1-b)^3 + 1056*(1-b)^4
          + 768*(1-b)^5 + 256*(1-b)^6 := by ring
    rw [hh]
    positivity
  linarith


/-! ### Derivatives of `dl2` -/

noncomputable def dd2 (b : ℝ) : ℝ := -2*(8*(1+b)^2-1)/(8*(1+b)^2+1)^2
noncomputable def d2d2 (b : ℝ) : ℝ := 32*(1+b)*(8*(1+b)^2-3)/(8*(1+b)^2+1)^3

/-- `d/db (2 + 2b) = 2`. -/
lemma hd_l2 (b : ℝ) : HasDerivAt (fun t : ℝ => 2*(1+t)) 2 b := by
  have hfun : (fun t : ℝ => 2*(1+t)) = (fun t : ℝ => 2*t + 2) := by funext t; ring
  rw [hfun]
  exact (hasDerivAt_lin (2:ℝ) 2 b).congr_deriv (by ring)

/-- `d/db (8(1+b)²+1) = 16(1+b)`. -/
lemma hd_d2 (b : ℝ) : HasDerivAt (fun t : ℝ => 8*(1+t)^2+1) (16*(1+b)) b := by
  have hfun : (fun t : ℝ => 8*(1+t)^2+1) = (fun t : ℝ => 8*t^2 + 16*t + 9) := by funext t; ring
  rw [hfun]
  exact (hasDerivAt_quad (9:ℝ) 16 8 b).congr_deriv (by ring)

/-- `d/db (-2(8(1+b)²-1))`. -/
lemma hd_n2 (b : ℝ) : HasDerivAt (fun t : ℝ => -2*(8*(1+t)^2-1)) (-2*(16*(1+b))) b := by
  have hfun : (fun t : ℝ => -2*(8*(1+t)^2-1)) = (fun t : ℝ => -16*t^2 + (-32)*t + (-14)) := by
    funext t; ring
  rw [hfun]
  exact (hasDerivAt_quad (-14:ℝ) (-32) (-16) b).congr_deriv (by ring)

/-- `d/db ((8(1+b)²+1)²)`. -/
lemma hd_d2sq (b : ℝ) : HasDerivAt (fun t : ℝ => (8*(1+t)^2+1)^2)
    (2*(8*(1+b)^2+1)*(16*(1+b))) b := by
  have hfun : (fun t : ℝ => (8*(1+t)^2+1)^2)
      = (fun t : ℝ => 64*t^4 + 256*t^3 + 400*t^2 + 288*t + 81) := by funext t; ring
  rw [hfun]
  exact (hasDerivAt_quart (81:ℝ) 288 400 256 64 b).congr_deriv (by ring)

lemma hasDerivAt_dl2 (b : ℝ) (h : (8*(1+b)^2+1) ≠ 0) : HasDerivAt dl2 (dd2 b) b := by
  have hdiv := (hd_l2 b).div (hd_d2 b) h
  unfold dl2
  have hfun : (fun t : ℝ => 2*(1+t)/(8*(1+t)^2+1)) = (fun t : ℝ => 2*(1+t)) / (fun t : ℝ => 8*(1+t)^2+1) := rfl
  rw [hfun]
  refine hdiv.congr_deriv ?_
  simp only [dd2]
  field_simp
  ring

lemma hasDerivAt_dd2 (b : ℝ) (h : (8*(1+b)^2+1) ≠ 0) : HasDerivAt dd2 (d2d2 b) b := by
  have hdiv := (hd_n2 b).div (hd_d2sq b) (pow_ne_zero 2 h)
  unfold dd2
  have hfun : (fun t : ℝ => -2*(8*(1+t)^2-1)/(8*(1+t)^2+1)^2)
      = (fun t : ℝ => -2*(8*(1+t)^2-1)) / (fun t : ℝ => (8*(1+t)^2+1)^2) := rfl
  rw [hfun]
  refine hdiv.congr_deriv ?_
  simp only [d2d2]
  field_simp
  ring

lemma d2d2_le {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : d2d2 b ≤ 1/4 := by
  have hid : d2d2 b
      = 32*(3/2+(b-1/2))*(15+24*(b-1/2)+8*(b-1/2)^2)/(19+24*(b-1/2)+8*(b-1/2)^2)^3 := by
    simp only [d2d2]; ring
  rw [hid]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (19+24*(b-1/2)+8*(b-1/2)^2)^3)]
  have hcert : (0:ℝ) ≤ (1/4)*(19+24*(b-1/2)+8*(b-1/2)^2)^3
      - 32*(3/2+(b-1/2))*(15+24*(b-1/2)+8*(b-1/2)^2) := by
    have hh : (1/4)*(19+24*(b-1/2)+8*(b-1/2)^2)^3
        - 32*(3/2+(b-1/2))*(15+24*(b-1/2)+8*(b-1/2)^2)
        = (3979/4:ℝ) + 4866*(b-1/2) + 9222*(b-1/2)^2 + 8672*(b-1/2)^3
          + 4368*(b-1/2)^4 + 1152*(b-1/2)^5 + 128*(b-1/2)^6 := by ring
    rw [hh]
    positivity
  linarith

/-! ### Derivatives of `dlr` -/

noncomputable def ddr (b : ℝ) : ℝ := 2*(8*(2-b)^2-1)/(8*(2-b)^2+1)^2
noncomputable def d2dr (b : ℝ) : ℝ := 32*(2-b)*(8*(2-b)^2-3)/(8*(2-b)^2+1)^3

/-- `d/db (4 - 2b) = -2`. -/
lemma hd_lr (b : ℝ) : HasDerivAt (fun t : ℝ => 2*(2-t)) (-2) b := by
  have hfun : (fun t : ℝ => 2*(2-t)) = (fun t : ℝ => (-2)*t + 4) := by funext t; ring
  rw [hfun]
  exact (hasDerivAt_lin (4:ℝ) (-2) b).congr_deriv (by ring)

/-- `d/db (8(2-b)²+1) = -16(2-b)`. -/
lemma hd_dr (b : ℝ) : HasDerivAt (fun t : ℝ => 8*(2-t)^2+1) (-16*(2-b)) b := by
  have hfun : (fun t : ℝ => 8*(2-t)^2+1) = (fun t : ℝ => 8*t^2 + (-32)*t + 33) := by funext t; ring
  rw [hfun]
  exact (hasDerivAt_quad (33:ℝ) (-32) 8 b).congr_deriv (by ring)

/-- `d/db (2(8(2-b)²-1))`. -/
lemma hd_nr (b : ℝ) : HasDerivAt (fun t : ℝ => 2*(8*(2-t)^2-1)) (-32*(2-b)) b := by
  have hfun : (fun t : ℝ => 2*(8*(2-t)^2-1)) = (fun t : ℝ => 16*t^2 + (-64)*t + 62) := by
    funext t; ring
  rw [hfun]
  exact (hasDerivAt_quad (62:ℝ) (-64) 16 b).congr_deriv (by ring)

/-- `d/db ((8(2-b)²+1)²)`. -/
lemma hd_drsq (b : ℝ) : HasDerivAt (fun t : ℝ => (8*(2-t)^2+1)^2)
    (2*(8*(2-b)^2+1)*(-16*(2-b))) b := by
  have hfun : (fun t : ℝ => (8*(2-t)^2+1)^2)
      = (fun t : ℝ => 64*t^4 + (-512)*t^3 + 1552*t^2 + (-2112)*t + 1089) := by funext t; ring
  rw [hfun]
  exact (hasDerivAt_quart (1089:ℝ) (-2112) 1552 (-512) 64 b).congr_deriv (by ring)

lemma hasDerivAt_dlr (b : ℝ) (h : (8*(2-b)^2+1) ≠ 0) : HasDerivAt dlr (ddr b) b := by
  have hdiv := (hd_lr b).div (hd_dr b) h
  unfold dlr
  have hfun : (fun t : ℝ => 2*(2-t)/(8*(2-t)^2+1)) = (fun t : ℝ => 2*(2-t)) / (fun t : ℝ => 8*(2-t)^2+1) := rfl
  rw [hfun]
  refine hdiv.congr_deriv ?_
  simp only [ddr]
  field_simp
  ring

lemma hasDerivAt_ddr (b : ℝ) (h : (8*(2-b)^2+1) ≠ 0) : HasDerivAt ddr (d2dr b) b := by
  have hdiv := (hd_nr b).div (hd_drsq b) (pow_ne_zero 2 h)
  unfold ddr
  have hfun : (fun t : ℝ => 2*(8*(2-t)^2-1)/(8*(2-t)^2+1)^2)
      = (fun t : ℝ => 2*(8*(2-t)^2-1)) / (fun t : ℝ => (8*(2-t)^2+1)^2) := rfl
  rw [hfun]
  refine hdiv.congr_deriv ?_
  simp only [d2dr]
  field_simp
  ring

lemma d2dr_le {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : d2dr b ≤ 1/4 := by
  have hid : d2dr b
      = 32*(1+(1-b))*(5+16*(1-b)+8*(1-b)^2)/(9+16*(1-b)+8*(1-b)^2)^3 := by
    simp only [d2dr]; ring
  rw [hid]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (9+16*(1-b)+8*(1-b)^2)^3)]
  have hcert : (0:ℝ) ≤ (1/4)*(9+16*(1-b)+8*(1-b)^2)^3
      - 32*(1+(1-b))*(5+16*(1-b)+8*(1-b)^2) := by
    have hh : (1/4)*(9+16*(1-b)+8*(1-b)^2)^3 - 32*(1+(1-b))*(5+16*(1-b)+8*(1-b)^2)
        = (89/4:ℝ) + 300*(1-b) + 1446*(1-b)^2 + 2496*(1-b)^3
          + 1968*(1-b)^4 + 768*(1-b)^5 + 128*(1-b)^6 := by ring
    rw [hh]
    positivity
  linarith


/-! ### Derivatives of `Ctot` -/

noncomputable def Ctot1 (b : ℝ) : ℝ := 2*(1-b)/(2-b)
noncomputable def Ctot2 (b : ℝ) : ℝ := (1-b)^2/(2-b)^3
noncomputable def Ctot3 (b : ℝ) : ℝ := (3/2)*(1-b)^3/(2-b)^5

lemma Ctot_eq (b : ℝ) (h : (0:ℝ) < 2-b) : Ctot b = Ctot1 b + Ctot2 b + Ctot3 b := by
  simp only [Ctot, Ctot1, Ctot2, Ctot3]
  field_simp
  ring

noncomputable def dCtot1 (b : ℝ) : ℝ := ((-2)*(2-b) - (2*(1-b))*(-1))/(2-b)^2
noncomputable def dCtot2 (b : ℝ) : ℝ :=
  ((2*b-2)*(2-b)^3 - (1-b)^2*(-3*b^2+12*b-12))/(((2-b)^3)^2)
noncomputable def dCtot3 (b : ℝ) : ℝ :=
  ((-(9/2)*b^2+9*b-(9/2))*(2-b)^5
    - ((3/2)*(1-b)^3)*(-5*b^4+40*b^3-120*b^2+160*b-80))/(((2-b)^5)^2)
noncomputable def dCtot (b : ℝ) : ℝ := dCtot1 b + dCtot2 b + dCtot3 b

lemma hasDerivAt_Ctot1 (b : ℝ) (h : (0:ℝ) < 2-b) :
    HasDerivAt Ctot1 (dCtot1 b) b := by
  have hnum : HasDerivAt (fun t : ℝ => 2*(1-t)) (-2) b := by
    have hfun : (fun t : ℝ => 2*(1-t)) = (fun t : ℝ => (-2)*t + 2) := by funext t; ring
    rw [hfun]
    exact (hasDerivAt_lin (2:ℝ) (-2) b).congr_deriv (by ring)
  have hden : HasDerivAt (fun t : ℝ => 2-t) (-1) b := by
    have hfun : (fun t : ℝ => 2-t) = (fun t : ℝ => (-1)*t + 2) := by funext t; ring
    rw [hfun]
    exact (hasDerivAt_lin (2:ℝ) (-1) b).congr_deriv (by ring)
  refine (hnum.div hden h.ne').congr_deriv ?_
  simp only [dCtot1]

lemma hasDerivAt_Ctot2 (b : ℝ) (h : (0:ℝ) < 2-b) :
    HasDerivAt Ctot2 (dCtot2 b) b := by
  have hnum : HasDerivAt (fun t : ℝ => (1-t)^2) (2*b-2) b := by
    have hh := hasDerivAt_quad (1:ℝ) (-2) 1 b
    convert hh using 1 <;> (first | (ext t; ring) | ring)
  have hden : HasDerivAt (fun t : ℝ => (2-t)^3) (-3*b^2+12*b-12) b := by
    have hh := hasDerivAt_cubic (8:ℝ) (-12) 6 (-1) b
    convert hh using 1 <;> (first | (ext t; ring) | ring)
  refine (hnum.div hden (pow_ne_zero 3 h.ne')).congr_deriv ?_
  simp only [dCtot2]

lemma hasDerivAt_Ctot3 (b : ℝ) (h : (0:ℝ) < 2-b) :
    HasDerivAt Ctot3 (dCtot3 b) b := by
  have hnum : HasDerivAt (fun t : ℝ => (3/2)*(1-t)^3) (-(9/2)*b^2+9*b-(9/2)) b := by
    have hh := hasDerivAt_cubic (3/2:ℝ) (-9/2) (9/2) (-3/2) b
    convert hh using 1 <;> (first | (ext t; ring) | ring)
  have hden : HasDerivAt (fun t : ℝ => (2-t)^5) (-5*b^4+40*b^3-120*b^2+160*b-80) b := by
    have hh := hasDerivAt_quint (32:ℝ) (-80) 80 (-40) 10 (-1) b
    convert hh using 1 <;> (first | (ext t; ring) | ring)
  refine (hnum.div hden (pow_ne_zero 5 h.ne')).congr_deriv ?_
  simp only [dCtot3]

lemma hasDerivAt_Ctot (b : ℝ) (h : (0:ℝ) < 2-b) : HasDerivAt Ctot (dCtot b) b := by
  have hC : Ctot = fun b : ℝ => Ctot1 b + Ctot2 b + Ctot3 b := by
    funext b; simp only [Ctot, Ctot1, Ctot2, Ctot3]
    field_simp
    ring
  rw [hC]
  have h1 := hasDerivAt_Ctot1 b h
  have h2 := hasDerivAt_Ctot2 b h
  have h3 := hasDerivAt_Ctot3 b h
  have hsum := (h1.add h2).add h3
  unfold dCtot
  exact hsum

noncomputable def d2Ctot1 (b : ℝ) : ℝ :=
  (0 * (2-b)^2 - ((-2)*(2-b) - (2*(1-b))*(-1)) * (2*b-4)) / (((2-b)^2)^2)
noncomputable def d2Ctot2 (b : ℝ) : ℝ :=
  ((4*b^3-12*b^2+6*b+4) * (((2-b)^3)^2)
    - ((2*b-2)*(2-b)^3 - (1-b)^2*(-3*b^2+12*b-12))
      * (2 * (2-b)^3 * (-3*b^2+12*b-12)))
    / ((((2-b)^3)^2)^2)
noncomputable def d2Ctot3 (b : ℝ) : ℝ :=
  (((-21)*b^6 + 171*b^5 - 540*b^4 + 810*b^3 - 540*b^2 + 72*b + 48) * (((2-b)^5)^2)
    - ((-(9/2)*b^2+9*b-(9/2))*(2-b)^5
      - ((3/2)*(1-b)^3)*(-5*b^4+40*b^3-120*b^2+160*b-80))
      * (2 * (2-b)^5 * (-5*b^4+40*b^3-120*b^2+160*b-80)))
    / ((((2-b)^5)^2)^2)
noncomputable def d2Ctot (b : ℝ) : ℝ := d2Ctot1 b + d2Ctot2 b + d2Ctot3 b

lemma hasDerivAt_dCtot1 (b : ℝ) (h : (0:ℝ) < 2-b) : HasDerivAt dCtot1 (d2Ctot1 b) b := by
  have hnum : HasDerivAt (fun t : ℝ => (-2)*(2-t) - (2*(1-t))*(-1)) 0 b := by
    have hh := hasDerivAt_lin (-2:ℝ) 0 b
    convert hh using 1 <;> (first | (ext t; ring) | ring)
  have hden : HasDerivAt (fun t : ℝ => (2-t)^2) (2*b-4) b := by
    have hh := hasDerivAt_quad (4:ℝ) (-4) 1 b
    convert hh using 1 <;> (first | (ext t; ring) | ring)
  have hfun : dCtot1 = (fun t : ℝ => (-2)*(2-t) - (2*(1-t))*(-1))
      / (fun t : ℝ => (2-t)^2) := by
    funext t; simp only [dCtot1, Pi.div_apply, Pi.pow_apply]
  rw [hfun]
  refine (hnum.div hden (by positivity)).congr_deriv ?_
  simp only [d2Ctot1]

lemma hasDerivAt_dCtot2 (b : ℝ) (h : (0:ℝ) < 2-b) : HasDerivAt dCtot2 (d2Ctot2 b) b := by
  have hnum : HasDerivAt (fun t : ℝ => (2*t-2)*(2-t)^3 - (1-t)^2*(-3*t^2+12*t-12))
      (4*b^3-12*b^2+6*b+4) b := by
    have hh := hasDerivAt_quart (-4:ℝ) 4 3 (-4) 1 b
    convert hh using 1 <;> (first | (ext t; ring) | ring)
  have hden : HasDerivAt (fun t : ℝ => ((2-t)^3)^2)
      (2 * (2-b)^3 * (-3*b^2+12*b-12)) b := by
    have h1 : HasDerivAt (fun t : ℝ => (2-t)^3) (-3*b^2+12*b-12) b := by
      have hh := hasDerivAt_cubic (8:ℝ) (-12) 6 (-1) b
      convert hh using 1 <;> (first | (ext t; ring) | ring)
    have h2 := h1.pow 2
    have hfun2 : (fun t : ℝ => ((2-t)^3)^2) = ((fun t : ℝ => (2-t)^3)^2) := by
      funext t; simp only [Pi.pow_apply]
    rw [hfun2]
    exact h2.congr_deriv (by ring)
  have hfun : dCtot2 = (fun t : ℝ => (2*t-2)*(2-t)^3 - (1-t)^2*(-3*t^2+12*t-12))
      / (fun t : ℝ => ((2-t)^3)^2) := by
    funext t; simp only [dCtot2, Pi.div_apply, Pi.pow_apply]
  rw [hfun]
  refine (hnum.div hden (by positivity)).congr_deriv ?_
  simp only [d2Ctot2]

lemma hasDerivAt_dCtot3 (b : ℝ) (h : (0:ℝ) < 2-b) : HasDerivAt dCtot3 (d2Ctot3 b) b := by
  have hnum : HasDerivAt (fun t : ℝ => (-(9/2)*t^2+9*t-(9/2))*(2-t)^5
        - ((3/2)*(1-t)^3)*(-5*t^4+40*t^3-120*t^2+160*t-80))
      ((-21)*b^6 + 171*b^5 - 540*b^4 + 810*b^3 - 540*b^2 + 72*b + 48) b := by
    have hh := hasDerivAt_sept (-24:ℝ) 48 36 (-180) (405/2) (-108) (57/2) (-3) b
    convert hh using 1 <;> (first | (ext t; ring) | ring)
  have hden : HasDerivAt (fun t : ℝ => ((2-t)^5)^2)
      (2 * (2-b)^5 * (-5*b^4+40*b^3-120*b^2+160*b-80)) b := by
    have h1 : HasDerivAt (fun t : ℝ => (2-t)^5) (-5*b^4+40*b^3-120*b^2+160*b-80) b := by
      have hh := hasDerivAt_quint (32:ℝ) (-80) 80 (-40) 10 (-1) b
      convert hh using 1 <;> (first | (ext t; ring) | ring)
    have h2 := h1.pow 2
    have hfun2 : (fun t : ℝ => ((2-t)^5)^2) = ((fun t : ℝ => (2-t)^5)^2) := by
      funext t; simp only [Pi.pow_apply]
    rw [hfun2]
    exact h2.congr_deriv (by ring)
  have hfun : dCtot3 = (fun t : ℝ => (-(9/2)*t^2+9*t-(9/2))*(2-t)^5
        - ((3/2)*(1-t)^3)*(-5*t^4+40*t^3-120*t^2+160*t-80))
      / (fun t : ℝ => ((2-t)^5)^2) := by
    funext t; simp only [dCtot3, Pi.div_apply, Pi.pow_apply]
  rw [hfun]
  refine (hnum.div hden (by positivity)).congr_deriv ?_
  simp only [d2Ctot3]

lemma hasDerivAt_dCtot (b : ℝ) (h : (0:ℝ) < 2-b) : HasDerivAt dCtot (d2Ctot b) b := by
  have h1 := hasDerivAt_dCtot1 b h
  have h2 := hasDerivAt_dCtot2 b h
  have h3 := hasDerivAt_dCtot3 b h
  unfold dCtot d2Ctot
  exact (h1.add h2).add h3

lemma dCtot_nice (b : ℝ) (h : (0:ℝ) < 2-b) :
    dCtot b = - (2 + 10*(1-b) + (39/2)*(1-b)^2 + 5*(1-b)^3 + (1-b)^4) / (2-b)^6 := by
  have e2 : (0:ℝ) < (2-b)^2 := by positivity
  have e3 : (0:ℝ) < (2-b)^3 := by positivity
  have e5 : (0:ℝ) < (2-b)^5 := by positivity
  have e6 : (0:ℝ) < (2-b)^6 := by positivity
  simp only [dCtot, dCtot1, dCtot2, dCtot3]
  field_simp
  ring_nf

lemma d2Ctot_nice (b : ℝ) (h : (0:ℝ) < 2-b) :
    d2Ctot b = (-2*(1-b)^4 - 11*(1-b)^3 - 63*(1-b)^2 - 11*(1-b) - 2)/(2-b)^7 := by
  have e2 : (0:ℝ) < (2-b)^2 := by positivity
  have e3 : (0:ℝ) < (2-b)^3 := by positivity
  have e4 : (0:ℝ) < (2-b)^4 := by positivity
  have e5 : (0:ℝ) < (2-b)^5 := by positivity
  have e6 : (0:ℝ) < (2-b)^6 := by positivity
  have e7 : (0:ℝ) < (2-b)^7 := by positivity
  simp only [d2Ctot, d2Ctot1, d2Ctot2, d2Ctot3]
  field_simp
  ring_nf

lemma d2Ctot_le {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : d2Ctot b ≤ 1/2 := by
  have hpos : (0:ℝ) < 2-b := by linarith
  rw [d2Ctot_nice b hpos]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (2-b)^7)]
  have hid2 : (2-b)^7 = (1+(1-b))^7 := by ring
  rw [hid2]
  have hcert : (0:ℝ) ≤ (1/2)*(1+(1-b))^7
      - (-2*(1-b)^4-11*(1-b)^3-63*(1-b)^2-11*(1-b)-2) := by
    have hh : (1/2)*(1+(1-b))^7 - (-2*(1-b)^4-11*(1-b)^3-63*(1-b)^2-11*(1-b)-2)
        = (5/2:ℝ) + (29/2)*(1-b) + (147/2)*(1-b)^2 + (57/2)*(1-b)^3
          + (39/2)*(1-b)^4 + (21/2)*(1-b)^5 + (7/2)*(1-b)^6 + (1/2)*(1-b)^7 := by ring
    rw [hh]
    positivity
  linarith

lemma dCtot_nonpos {b : ℝ} (h2 : b ≤ 1) : dCtot b ≤ 0 := by
  have hpos : (0:ℝ) < 2-b := by linarith
  rw [dCtot_nice b hpos]
  have hu : (0:ℝ) ≤ 1-b := by linarith
  have hnum : (0:ℝ) ≤ 2 + 10*(1-b) + (39/2)*(1-b)^2 + 5*(1-b)^3 + (1-b)^4 := by positivity
  have hden : (0:ℝ) < (2-b)^6 := by positivity
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hnum) hden.le

lemma Ctot_nonneg {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : 0 ≤ Ctot b := by
  have hpos : (0:ℝ) < 2-b := by linarith
  rw [Ctot_eq b hpos]
  simp only [Ctot1, Ctot2, Ctot3]
  have hu : (0:ℝ) ≤ 1-b := by linarith
  positivity

lemma Ctot_le {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : Ctot b ≤ 2 := by
  have hpos : (0:ℝ) < 2-b := by linarith
  rw [Ctot_eq b hpos]
  simp only [Ctot1, Ctot2, Ctot3]
  have hu : (0:ℝ) ≤ 1-b := by linarith
  have hu1 : 1-b ≤ 1/2 := by linarith
  have hd : (0:ℝ) < 2-b := by linarith
  have h1' : 2*(1-b)/(2-b) ≤ 1 := by
    rw [div_le_iff₀ hd]; linarith
  have h2' : (1-b)^2/(2-b)^3 ≤ 1/4 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (2-b)^3)]
    nlinarith [sq_nonneg (1-b), hu, hu1, sq_nonneg (1-b-1/2)]
  have h3' : (3/2)*(1-b)^3/(2-b)^5 ≤ 3/16 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (2-b)^5)]
    have hb2 : (1-b)^3 ≤ 1/8 := by nlinarith [pow_le_pow_left₀ hu hu1 3]
    have hb1 : (1:ℝ) ≤ (2-b)^5 := by
      have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) (by linarith : (1:ℝ) ≤ 2-b) 5
      simpa using this
    nlinarith [hb1, hb2, show (0:ℝ) ≤ (2-b)^5 by positivity]
  linarith

/-! ### Power helpers for `(2-t)^k` -/

lemma hasDerivAt_2ms2 (x : ℝ) : HasDerivAt (fun t : ℝ => (2-t)^2) (2*(1)*x^1 + (-4)) x := by
  have hh := hasDerivAt_quad (4 : ℝ) (-4 : ℝ) (1 : ℝ) x
  convert hh using 1 <;> (first | (ext t; ring) | ring)

lemma hasDerivAt_2ms3 (x : ℝ) : HasDerivAt (fun t : ℝ => (2-t)^3) (3*(-1)*x^2 + 2*(6)*x^1 + (-12)) x := by
  have hh := hasDerivAt_cubic (8 : ℝ) (-12 : ℝ) (6 : ℝ) (-1 : ℝ) x
  convert hh using 1 <;> (first | (ext t; ring) | ring)

lemma hasDerivAt_2ms4 (x : ℝ) : HasDerivAt (fun t : ℝ => (2-t)^4) (4*(1)*x^3 + 3*(-8)*x^2 + 2*(24)*x^1 + (-32)) x := by
  have hh := hasDerivAt_quart (16 : ℝ) (-32 : ℝ) (24 : ℝ) (-8 : ℝ) (1 : ℝ) x
  convert hh using 1 <;> (first | (ext t; ring) | ring)

lemma hasDerivAt_2ms5 (x : ℝ) : HasDerivAt (fun t : ℝ => (2-t)^5) (5*(-1)*x^4 + 4*(10)*x^3 + 3*(-40)*x^2 + 2*(80)*x^1 + (-80)) x := by
  have hh := hasDerivAt_quint (32 : ℝ) (-80 : ℝ) (80 : ℝ) (-40 : ℝ) (10 : ℝ) (-1 : ℝ) x
  convert hh using 1 <;> (first | (ext t; ring) | ring)

lemma hasDerivAt_2ms6 (x : ℝ) : HasDerivAt (fun t : ℝ => (2-t)^6) (6*(1)*x^5 + 5*(-12)*x^4 + 4*(60)*x^3 + 3*(-160)*x^2 + 2*(240)*x^1 + (-192)) x := by
  have hh := hasDerivAt_sext (64 : ℝ) (-192 : ℝ) (240 : ℝ) (-160 : ℝ) (60 : ℝ) (-12 : ℝ) (1 : ℝ) x
  convert hh using 1 <;> (first | (ext t; ring) | ring)

lemma hasDerivAt_2ms7 (x : ℝ) : HasDerivAt (fun t : ℝ => (2-t)^7) (7*(-1)*x^6 + 6*(14)*x^5 + 5*(-84)*x^4 + 4*(280)*x^3 + 3*(-560)*x^2 + 2*(672)*x^1 + (-448)) x := by
  have hh := hasDerivAt_sept (128 : ℝ) (-448 : ℝ) (672 : ℝ) (-560 : ℝ) (280 : ℝ) (-84 : ℝ) (14 : ℝ) (-1 : ℝ) x
  convert hh using 1 <;> (first | (ext t; ring) | ring)

lemma hasDerivAt_2ms8 (x : ℝ) : HasDerivAt (fun t : ℝ => (2-t)^8) (8*(1)*x^7 + 7*(-16)*x^6 + 6*(112)*x^5 + 5*(-448)*x^4 + 4*(1120)*x^3 + 3*(-1792)*x^2 + 2*(1792)*x^1 + (-1024)) x := by
  have hh := hasDerivAt_oct (256 : ℝ) (-1024 : ℝ) (1792 : ℝ) (-1792 : ℝ) (1120 : ℝ) (-448 : ℝ) (112 : ℝ) (-16 : ℝ) (1 : ℝ) x
  convert hh using 1 <;> (first | (ext t; ring) | ring)

lemma hasDerivAt_2ms9 (x : ℝ) : HasDerivAt (fun t : ℝ => (2-t)^9)
    (9*(2-x)^8*(-1)) x := by
  have hfun : (fun t : ℝ => (2-t)^9) = ((fun t : ℝ => (2-t)^8) * (fun t : ℝ => 2-t)) := by
    funext t; simp only [Pi.mul_apply]; ring
  rw [hfun]
  have h2 : HasDerivAt (fun t : ℝ => 2-t) (-1) x := by
    have hh := hasDerivAt_lin (2:ℝ) (-1) x
    convert hh using 1 <;> (first | (ext t; ring) | ring)
  refine ((hasDerivAt_2ms8 x).mul h2).congr_deriv ?_
  ring

lemma hasDerivAt_2ms10 (x : ℝ) : HasDerivAt (fun t : ℝ => (2-t)^10)
    (10*(2-x)^9*(-1)) x := by
  have hfun : (fun t : ℝ => (2-t)^10) = ((fun t : ℝ => (2-t)^9) * (fun t : ℝ => 2-t)) := by
    funext t; simp only [Pi.mul_apply]; ring
  rw [hfun]
  have h2 : HasDerivAt (fun t : ℝ => 2-t) (-1) x := by
    have hh := hasDerivAt_lin (2:ℝ) (-1) x
    convert hh using 1 <;> (first | (ext t; ring) | ring)
  refine ((hasDerivAt_2ms9 x).mul h2).congr_deriv ?_
  ring

/-! ### Derivatives of `stuff1f` -/

noncomputable def s1c1 : ℝ := 7/768 - l2lo/128 - 7/2304
noncomputable def s1c2 : ℝ := -93/163840
noncomputable def s1c3 : ℝ := 635/44040192
noncomputable def s1c4 : ℝ := -511/1811939328

lemma stuff1f_funeq : stuff1f = fun b : ℝ =>
    1/4 + s1c1/(2-b)^2 + s1c2/(2-b)^4 + s1c3/(2-b)^6 + s1c4/(2-b)^8 := by
  funext b
  rcases eq_or_ne (2-b) 0 with hb | hb
  · simp only [stuff1f, K1pf, s1c1, s1c2, s1c3, s1c4, hb, div_zero, mul_zero, add_zero, sub_zero,
      neg_zero]
    norm_num
  · have h2 : (2-b)^2 ≠ 0 := pow_ne_zero 2 hb
    have h4 : (2-b)^4 ≠ 0 := pow_ne_zero 4 hb
    have h6 : (2-b)^6 ≠ 0 := pow_ne_zero 6 hb
    have h8 : (2-b)^8 ≠ 0 := pow_ne_zero 8 hb
    simp only [stuff1f, K1pf, s1c1, s1c2, s1c3, s1c4]
    field_simp
    ring

lemma hd_c2ms2 (c b : ℝ) (h : (0:ℝ) < 2-b) :
    HasDerivAt (fun t : ℝ => c/(2-t)^2) (c*2/(2-b)^3) b := by
  have hnum : HasDerivAt (fun _ : ℝ => c) 0 b := hasDerivAt_const b c
  refine ((hnum.div (hasDerivAt_2ms2 b) (by positivity))).congr_deriv ?_
  have e1 : (0:ℝ) < (2-b)^2 := by positivity
  have e2 : (0:ℝ) < (2-b)^3 := by positivity
  field_simp
  ring

lemma hd_c2ms3 (c b : ℝ) (h : (0:ℝ) < 2-b) :
    HasDerivAt (fun t : ℝ => c/(2-t)^3) (c*3/(2-b)^4) b := by
  have hnum : HasDerivAt (fun _ : ℝ => c) 0 b := hasDerivAt_const b c
  refine ((hnum.div (hasDerivAt_2ms3 b) (by positivity))).congr_deriv ?_
  have e1 : (0:ℝ) < (2-b)^3 := by positivity
  have e2 : (0:ℝ) < (2-b)^4 := by positivity
  field_simp
  ring

lemma hd_c2ms4 (c b : ℝ) (h : (0:ℝ) < 2-b) :
    HasDerivAt (fun t : ℝ => c/(2-t)^4) (c*4/(2-b)^5) b := by
  have hnum : HasDerivAt (fun _ : ℝ => c) 0 b := hasDerivAt_const b c
  refine ((hnum.div (hasDerivAt_2ms4 b) (by positivity))).congr_deriv ?_
  have e1 : (0:ℝ) < (2-b)^4 := by positivity
  have e2 : (0:ℝ) < (2-b)^5 := by positivity
  field_simp
  ring

lemma hd_c2ms5 (c b : ℝ) (h : (0:ℝ) < 2-b) :
    HasDerivAt (fun t : ℝ => c/(2-t)^5) (c*5/(2-b)^6) b := by
  have hnum : HasDerivAt (fun _ : ℝ => c) 0 b := hasDerivAt_const b c
  refine ((hnum.div (hasDerivAt_2ms5 b) (by positivity))).congr_deriv ?_
  have e1 : (0:ℝ) < (2-b)^5 := by positivity
  have e2 : (0:ℝ) < (2-b)^6 := by positivity
  field_simp
  ring

lemma hd_c2ms6 (c b : ℝ) (h : (0:ℝ) < 2-b) :
    HasDerivAt (fun t : ℝ => c/(2-t)^6) (c*6/(2-b)^7) b := by
  have hnum : HasDerivAt (fun _ : ℝ => c) 0 b := hasDerivAt_const b c
  refine ((hnum.div (hasDerivAt_2ms6 b) (by positivity))).congr_deriv ?_
  have e1 : (0:ℝ) < (2-b)^6 := by positivity
  have e2 : (0:ℝ) < (2-b)^7 := by positivity
  field_simp
  ring

lemma hd_c2ms7 (c b : ℝ) (h : (0:ℝ) < 2-b) :
    HasDerivAt (fun t : ℝ => c/(2-t)^7) (c*7/(2-b)^8) b := by
  have hnum : HasDerivAt (fun _ : ℝ => c) 0 b := hasDerivAt_const b c
  refine ((hnum.div (hasDerivAt_2ms7 b) (by positivity))).congr_deriv ?_
  have e1 : (0:ℝ) < (2-b)^7 := by positivity
  have e2 : (0:ℝ) < (2-b)^8 := by positivity
  field_simp
  ring

lemma hd_c2ms8 (c b : ℝ) (h : (0:ℝ) < 2-b) :
    HasDerivAt (fun t : ℝ => c/(2-t)^8) (c*8/(2-b)^9) b := by
  have hnum : HasDerivAt (fun _ : ℝ => c) 0 b := hasDerivAt_const b c
  refine ((hnum.div (hasDerivAt_2ms8 b) (by positivity))).congr_deriv ?_
  have e1 : (0:ℝ) < (2-b)^8 := by positivity
  have e2 : (0:ℝ) < (2-b)^9 := by positivity
  field_simp
  ring

lemma hd_c2ms9 (c b : ℝ) (h : (0:ℝ) < 2-b) :
    HasDerivAt (fun t : ℝ => c/(2-t)^9) (c*9/(2-b)^10) b := by
  have hnum : HasDerivAt (fun _ : ℝ => c) 0 b := hasDerivAt_const b c
  refine ((hnum.div (hasDerivAt_2ms9 b) (by positivity))).congr_deriv ?_
  have e1 : (0:ℝ) < (2-b)^9 := by positivity
  have e2 : (0:ℝ) < (2-b)^10 := by positivity
  field_simp
  ring

lemma hd_c2ms10 (c b : ℝ) (h : (0:ℝ) < 2-b) :
    HasDerivAt (fun t : ℝ => c/(2-t)^10) (c*10/(2-b)^11) b := by
  have hnum : HasDerivAt (fun _ : ℝ => c) 0 b := hasDerivAt_const b c
  refine ((hnum.div (hasDerivAt_2ms10 b) (by positivity))).congr_deriv ?_
  have e1 : (0:ℝ) < (2-b)^10 := by positivity
  have e2 : (0:ℝ) < (2-b)^11 := by positivity
  field_simp
  ring

noncomputable def dStuff1f (b : ℝ) : ℝ :=
  s1c1*2/(2-b)^3 + s1c2*4/(2-b)^5 + s1c3*6/(2-b)^7 + s1c4*8/(2-b)^9
noncomputable def d2Stuff1f (b : ℝ) : ℝ :=
  s1c1*6/(2-b)^4 + s1c2*20/(2-b)^6 + s1c3*42/(2-b)^8 + s1c4*72/(2-b)^10

lemma hasDerivAt_stuff1f (b : ℝ) (h : (0:ℝ) < 2-b) : HasDerivAt stuff1f (dStuff1f b) b := by
  rw [stuff1f_funeq]
  have hc : HasDerivAt (fun _ : ℝ => (1/4:ℝ)) 0 b := hasDerivAt_const b _
  have h1 := hd_c2ms2 s1c1 b h
  have h2 := hd_c2ms4 s1c2 b h
  have h3 := hd_c2ms6 s1c3 b h
  have h4 := hd_c2ms8 s1c4 b h
  have hsum := ((hc.add h1).add h2).add h3 |>.add h4
  have hfun : (fun b : ℝ => 1/4 + s1c1/(2-b)^2 + s1c2/(2-b)^4 + s1c3/(2-b)^6 + s1c4/(2-b)^8)
      = ((((fun _ : ℝ => (1/4:ℝ)) + fun t : ℝ => s1c1/(2-t)^2) + fun t : ℝ => s1c2/(2-t)^4)
        + fun t : ℝ => s1c3/(2-t)^6) + fun t : ℝ => s1c4/(2-t)^8 := by
    funext t; simp only [Pi.add_apply]
  rw [hfun]
  have hv : (0:ℝ) + s1c1*2/(2-b)^3 + s1c2*4/(2-b)^5 + s1c3*6/(2-b)^7 + s1c4*8/(2-b)^9
      = dStuff1f b := by simp only [dStuff1f]; ring
  exact hsum.congr_deriv hv

lemma hasDerivAt_dStuff1f (b : ℝ) (h : (0:ℝ) < 2-b) : HasDerivAt dStuff1f (d2Stuff1f b) b := by
  unfold dStuff1f
  have h1 : HasDerivAt (fun t : ℝ => s1c1*2/(2-t)^3) (s1c1*6/(2-b)^4) b := by
    have hh := hd_c2ms3 (s1c1*2) b h
    convert hh using 1 <;> (first | (ext t; ring) | ring)
  have h2 : HasDerivAt (fun t : ℝ => s1c2*4/(2-t)^5) (s1c2*20/(2-b)^6) b := by
    have hh := hd_c2ms5 (s1c2*4) b h
    convert hh using 1 <;> (first | (ext t; ring) | ring)
  have h3 : HasDerivAt (fun t : ℝ => s1c3*6/(2-t)^7) (s1c3*42/(2-b)^8) b := by
    have hh := hd_c2ms7 (s1c3*6) b h
    convert hh using 1 <;> (first | (ext t; ring) | ring)
  have h4 : HasDerivAt (fun t : ℝ => s1c4*8/(2-t)^9) (s1c4*72/(2-b)^10) b := by
    have hh := hd_c2ms9 (s1c4*8) b h
    convert hh using 1 <;> (first | (ext t; ring) | ring)
  have hsum := ((h1.add h2).add h3).add h4
  have hfun : (fun b : ℝ => s1c1*2/(2-b)^3 + s1c2*4/(2-b)^5 + s1c3*6/(2-b)^7 + s1c4*8/(2-b)^9)
      = (((fun t : ℝ => s1c1*2/(2-t)^3) + fun t : ℝ => s1c2*4/(2-t)^5)
        + fun t : ℝ => s1c3*6/(2-t)^7) + fun t : ℝ => s1c4*8/(2-t)^9 := by
    funext t; simp only [Pi.add_apply]
  rw [hfun]
  have hv : s1c1*6/(2-b)^4 + s1c2*20/(2-b)^6 + s1c3*42/(2-b)^8 + s1c4*72/(2-b)^10
      = d2Stuff1f b := by simp only [d2Stuff1f]
  exact hsum.congr_deriv hv

lemma d2Stuff1f_bounds {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) :
    -(1:ℝ)/50 ≤ d2Stuff1f b ∧ d2Stuff1f b ≤ 1/50 := by
  have hA : (1:ℝ) ≤ 2-b := by linarith
  have hA2 : (2-b) ≤ 2 := by linarith
  have hA0 : (0:ℝ) < 2-b := by linarith
  have hc1 : (0:ℝ) ≤ s1c1*6 := by norm_num [s1c1, l2lo]
  have hc2 : s1c2*20 ≤ 0 := by norm_num [s1c2]
  have hc3 : (0:ℝ) ≤ s1c3*42 := by norm_num [s1c3]
  have hc4 : s1c4*72 ≤ 0 := by norm_num [s1c4]
  have e4 : (1:ℝ) ≤ (2-b)^4 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hA 4; simpa using this
  have e6 : (1:ℝ) ≤ (2-b)^6 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hA 6; simpa using this
  have e8 : (1:ℝ) ≤ (2-b)^8 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hA 8; simpa using this
  have e10 : (1:ℝ) ≤ (2-b)^10 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hA 10; simpa using this
  have f4 : (2-b)^4 ≤ 16 := by
    have := pow_le_pow_left₀ hA0.le hA2 4; norm_num at this ⊢; exact this
  have f6 : (2-b)^6 ≤ 64 := by
    have := pow_le_pow_left₀ hA0.le hA2 6; norm_num at this ⊢; exact this
  have f8 : (2-b)^8 ≤ 256 := by
    have := pow_le_pow_left₀ hA0.le hA2 8; norm_num at this ⊢; exact this
  have f10 : (2-b)^10 ≤ 1024 := by
    have := pow_le_pow_left₀ hA0.le hA2 10; norm_num at this ⊢; exact this
  unfold d2Stuff1f
  constructor
  · have p1 : s1c1*6/16 ≤ s1c1*6/(2-b)^4 :=
      div_le_div_of_nonneg_left hc1 (by positivity : (0:ℝ) < (2-b)^4) f4
    have p2 : s1c2*20 ≤ s1c2*20/(2-b)^6 := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < (2-b)^6)]
      nlinarith [hc2, e6]
    have p3 : s1c3*42/256 ≤ s1c3*42/(2-b)^8 :=
      div_le_div_of_nonneg_left hc3 (by positivity : (0:ℝ) < (2-b)^8) f8
    have p4 : s1c4*72 ≤ s1c4*72/(2-b)^10 := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < (2-b)^10)]
      nlinarith [hc4, e10]
    have hnum : -(1:ℝ)/50 ≤ s1c1*6/16 + s1c2*20 + s1c3*42/256 + s1c4*72 := by
      norm_num [s1c1, s1c2, s1c3, s1c4, l2lo]
    linarith
  · have q1 : s1c1*6/(2-b)^4 ≤ s1c1*6 := div_le_self hc1 e4
    have q2 : s1c2*20/(2-b)^6 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hc2 (by positivity)
    have q3 : s1c3*42/(2-b)^8 ≤ s1c3*42 := div_le_self hc3 e8
    have q4 : s1c4*72/(2-b)^10 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hc4 (by positivity)
    have hnum : s1c1*6 + 0 + s1c3*42 + 0 ≤ (1:ℝ)/50 := by
      norm_num [s1c1, s1c3, l2lo]
    linarith


/-! ### Derivatives of `LAf` and `LBf` -/

noncomputable def dLAf (b : ℝ) : ℝ := -∑ k ∈ Finset.range 10, (b/2)^k/2
noncomputable def d2LAf (b : ℝ) : ℝ := -∑ k ∈ Finset.range 10, (k:ℝ)*(b/2)^(k-1)/4

lemma hasDerivAt_LAf (b : ℝ) : HasDerivAt LAf (dLAf b) b := by
  have hterm : ∀ k ∈ Finset.range 10,
      HasDerivAt (fun t : ℝ => (t/2)^(k+1)/((k:ℝ)+1)) ((b/2)^k/2) b := by
    intro k hk
    have h1 : HasDerivAt (fun t : ℝ => t/2) (1/2) b := (hasDerivAt_id b).div_const 2
    have h3 := h1.pow (k+1)
    have h4 : HasDerivAt (fun t : ℝ => (t/2)^(k+1)) ((k+1:ℕ) * (b/2)^(k+1-1) * (1/2)) b := by
      convert h3 using 1 <;> (first | (ext t; simp only [Pi.pow_apply]) | ring)
    have h5 := h4.div_const ((k:ℝ)+1)
    have hv : ((k+1:ℕ) * (b/2)^(k+1-1) * (1/2))/((k:ℝ)+1) = (b/2)^k/2 := by
      rw [Nat.add_sub_cancel]
      push_cast
      have hk1 : ((k:ℝ)+1) ≠ 0 := by positivity
      field_simp
    exact h5.congr_deriv hv
  have hsum := HasDerivAt.sum hterm
  have hfinal := (hasDerivAt_const b (2*l2hi)).sub hsum
  have hfun : LAf = (fun _ : ℝ => 2*l2hi)
      - (fun b : ℝ => ∑ k ∈ Finset.range 10, (b/2)^(k+1)/((k:ℝ)+1)) := rfl
  rw [hfun]
  refine hfinal.congr_deriv ?_
  simp only [dLAf, zero_sub]

lemma hasDerivAt_dLAf (b : ℝ) : HasDerivAt dLAf (d2LAf b) b := by
  have hterm : ∀ k ∈ Finset.range 10,
      HasDerivAt (fun t : ℝ => (t/2)^k/2) ((k:ℝ)*(b/2)^(k-1)/4) b := by
    intro k hk
    have h1 : HasDerivAt (fun t : ℝ => t/2) (1/2) b := (hasDerivAt_id b).div_const 2
    have h3 := h1.pow k
    have h4 : HasDerivAt (fun t : ℝ => (t/2)^k) ((k:ℝ) * (b/2)^(k-1) * (1/2)) b := by
      convert h3 using 1 <;> (first | (ext t; simp only [Pi.pow_apply]) | ring)
    have h5 := h4.div_const 2
    have hv : ((k:ℝ) * (b/2)^(k-1) * (1/2))/2 = (k:ℝ)*(b/2)^(k-1)/4 := by ring_nf
    exact h5.congr_deriv hv
  have hsum := HasDerivAt.sum hterm
  have hfun : dLAf = (fun b : ℝ => - ∑ k ∈ Finset.range 10, (b/2)^k/2) := rfl
  rw [hfun]
  exact hsum.neg.congr_deriv (by simp only [d2LAf])

lemma LAf_bounds {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1) :
    LAf b ≤ 2 ∧ dLAf b ≤ 0 ∧ -(1:ℝ) ≤ d2LAf b := by
  have hb : (0:ℝ) ≤ b/2 := by linarith
  have hb1 : b/2 ≤ 1/2 := by linarith
  have hlt : l2hi ≤ 1 := by norm_num [l2hi]
  refine ⟨?_, ?_, ?_⟩
  · have hLeq : LAf b = 2*l2hi - ∑ k ∈ Finset.range 10, (b/2)^(k+1)/((k:ℝ)+1) := rfl
    rw [hLeq]
    have hnn : (0:ℝ) ≤ ∑ k ∈ Finset.range 10, (b/2)^(k+1)/((k:ℝ)+1) := by positivity
    linarith
  · have hdLeq : dLAf b = -∑ k ∈ Finset.range 10, (b/2)^k/2 := rfl
    rw [hdLeq, neg_nonpos]
    positivity
  · have hd2Leq : d2LAf b = -∑ k ∈ Finset.range 10, (k:ℝ)*(b/2)^(k-1)/4 := rfl
    rw [hd2Leq, neg_le_neg_iff]
    calc (∑ k ∈ Finset.range 10, (k:ℝ)*(b/2)^(k-1)/4)
        ≤ ∑ k ∈ Finset.range 10, (k:ℝ)*((1:ℝ)/2^(k-1))/4 := by
          apply Finset.sum_le_sum
          intro k hk
          have hkb : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
          have hpow : (b/2)^(k-1) ≤ (1:ℝ)/2^(k-1) := by
            have h2 := pow_le_pow_left₀ hb hb1 (k-1)
            calc (b/2)^(k-1) ≤ (1/2)^(k-1) := h2
              _ = (1:ℝ)/2^(k-1) := by rw [div_pow]; norm_num
          nlinarith [hkb, hpow]
      _ ≤ 1 := by norm_num [Finset.sum_range_succ]

noncomputable def dLBf (b : ℝ) : ℝ := ∑ k ∈ Finset.range 12, (1-b)^k
noncomputable def d2LBf (b : ℝ) : ℝ := -∑ k ∈ Finset.range 12, (k:ℝ)*(1-b)^(k-1)

lemma hasDerivAt_LBf (b : ℝ) : HasDerivAt LBf (dLBf b) b := by
  have hterm : ∀ k ∈ Finset.range 12,
      HasDerivAt (fun t : ℝ => (1-t)^(k+1)/((k:ℝ)+1)) (-(1-b)^k) b := by
    intro k hk
    have h1 : HasDerivAt (fun t : ℝ => 1-t) (-1) b := by
      have hh := hasDerivAt_lin (1:ℝ) (-1) b
      convert hh using 1 <;> (first | (ext t; ring) | ring)
    have h3 := h1.pow (k+1)
    have h4 : HasDerivAt (fun t : ℝ => (1-t)^(k+1)) ((k+1:ℕ) * (1-b)^(k+1-1) * (-1)) b := by
      convert h3 using 1 <;> (first | (ext t; simp only [Pi.pow_apply]) | ring)
    have h5 := h4.div_const ((k:ℝ)+1)
    have hv : ((k+1:ℕ) * (1-b)^(k+1-1) * (-1))/((k:ℝ)+1) = -(1-b)^k := by
      rw [Nat.add_sub_cancel]; push_cast
      have hk1 : ((k:ℝ)+1) ≠ 0 := by positivity
      field_simp
    exact h5.congr_deriv hv
  have hsum := HasDerivAt.sum hterm
  have hfinal := (hasDerivAt_const b l2hi).sub hsum
  have hfun : LBf = (fun _ : ℝ => l2hi)
      - (fun b : ℝ => ∑ k ∈ Finset.range 12, (1-b)^(k+1)/((k:ℝ)+1)) := rfl
  rw [hfun]
  refine hfinal.congr_deriv ?_
  simp only [dLBf, zero_sub, ← Finset.sum_neg_distrib]
  simp only [neg_neg]

lemma hasDerivAt_dLBf (b : ℝ) : HasDerivAt dLBf (d2LBf b) b := by
  have hterm : ∀ k ∈ Finset.range 12,
      HasDerivAt (fun t : ℝ => (1-t)^k) (-(k:ℝ)*(1-b)^(k-1)) b := by
    intro k hk
    have h1 : HasDerivAt (fun t : ℝ => 1-t) (-1) b := by
      have hh := hasDerivAt_lin (1:ℝ) (-1) b
      convert hh using 1 <;> (first | (ext t; ring) | ring)
    have h3 := h1.pow k
    have h4 : HasDerivAt (fun t : ℝ => (1-t)^k) ((k:ℝ) * (1-b)^(k-1) * (-1)) b := by
      convert h3 using 1 <;> (first | (ext t; simp only [Pi.pow_apply]) | ring)
    have hv : (k:ℝ) * (1-b)^(k-1) * (-1) = -(k:ℝ)*(1-b)^(k-1) := by ring_nf
    exact h4.congr_deriv hv
  have hsum := HasDerivAt.sum hterm
  have hfun : dLBf = (fun b : ℝ => ∑ k ∈ Finset.range 12, (1-b)^k) := rfl
  rw [hfun]
  refine hsum.congr_deriv ?_
  simp only [d2LBf, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  ring

lemma LBf_bounds {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) :
    LBf b ≤ 2 ∧ 0 ≤ dLBf b ∧ dLBf b ≤ 2 ∧ d2LBf b ≤ 0 ∧ -(4:ℝ) ≤ d2LBf b := by
  have hb : (0:ℝ) ≤ 1-b := by linarith
  have hb1 : 1-b ≤ 1/2 := by linarith
  have hlt : l2hi ≤ 1 := by norm_num [l2hi]
  have hsum1 : (∑ k ∈ Finset.range 12, (1:ℝ)/2^k) ≤ 2 := by
    norm_num [Finset.sum_range_succ]
  have hsum2 : (∑ k ∈ Finset.range 12, (k:ℝ)*((1:ℝ)/2^(k-1))) ≤ 4 := by
    norm_num [Finset.sum_range_succ]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hLeq : LBf b = l2hi - ∑ k ∈ Finset.range 12, (1-b)^(k+1)/((k:ℝ)+1) := rfl
    rw [hLeq]
    have hnn : (0:ℝ) ≤ ∑ k ∈ Finset.range 12, (1-b)^(k+1)/((k:ℝ)+1) := by positivity
    linarith
  · have hdLeq : dLBf b = ∑ k ∈ Finset.range 12, (1-b)^k := rfl
    rw [hdLeq]
    positivity
  · have hdLeq : dLBf b = ∑ k ∈ Finset.range 12, (1-b)^k := rfl
    rw [hdLeq]
    calc (∑ k ∈ Finset.range 12, (1-b)^k) ≤ ∑ k ∈ Finset.range 12, (1:ℝ)/2^k := by
          apply Finset.sum_le_sum
          intro k hk
          calc (1-b)^k ≤ (1/2)^k := pow_le_pow_left₀ hb hb1 k
            _ = (1:ℝ)/2^k := by rw [div_pow]; norm_num
      _ ≤ 2 := hsum1
  · have hd2Leq : d2LBf b = -∑ k ∈ Finset.range 12, (k:ℝ)*(1-b)^(k-1) := rfl
    rw [hd2Leq, neg_nonpos]
    apply Finset.sum_nonneg
    intro k hk
    have hkb : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    have := pow_nonneg hb (k-1)
    nlinarith [hkb, this]
  · have hd2Leq : d2LBf b = -∑ k ∈ Finset.range 12, (k:ℝ)*(1-b)^(k-1) := rfl
    rw [hd2Leq, neg_le_neg_iff]
    calc (∑ k ∈ Finset.range 12, (k:ℝ)*(1-b)^(k-1))
        ≤ ∑ k ∈ Finset.range 12, (k:ℝ)*((1:ℝ)/2^(k-1)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkb : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
          have hpow : (1-b)^(k-1) ≤ (1:ℝ)/2^(k-1) := by
            have h2' := pow_le_pow_left₀ hb hb1 (k-1)
            calc (1-b)^(k-1) ≤ (1/2)^(k-1) := h2'
              _ = (1:ℝ)/2^(k-1) := by rw [div_pow]; norm_num
          nlinarith [hkb, hpow]
      _ ≤ 4 := hsum2

/-! ### Derivatives of `stuff2f` -/

noncomputable def SS (b : ℝ) : ℝ := (2-b)^2 + b^2

lemma hasDerivAt_SS (b : ℝ) : HasDerivAt SS (4*b-4) b := by
  have hh := hasDerivAt_quad (4:ℝ) (-4) 2 b
  convert hh using 1 <;> (first | (ext t; simp only [SS]; ring) | ring)

noncomputable def s2C0 : ℝ := -l2lo/64 - 7/1152
noncomputable def s2C1 : ℝ := 7/768
noncomputable def s2C2 : ℝ := -31/163840
noncomputable def s2C3 : ℝ := 127/22020096
noncomputable def s2D1 : ℝ := -31/40960
noncomputable def s2D2 : ℝ := 127/7340032
noncomputable def s2D3 : ℝ := -511/905969664

lemma stuff2f_funeq : stuff2f = fun b : ℝ =>
    1/4 + s2C0/SS b + s2C1/b^2 + s2C2/b^4 + s2C3/b^6
      + s2D1/(b^2*SS b) + s2D2/(b^4*SS b) + s2D3/(b^6*SS b) := by
  funext b
  rcases eq_or_ne b 0 with hb | hb
  · subst hb
    simp only [stuff2f, K2pf, s2C0, s2C1, s2C2, s2C3, s2D1, s2D2, s2D3, SS, l2lo, div_zero, mul_zero,
      zero_mul, add_zero, sub_zero, zero_pow, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true]
    norm_num
  · have hS : SS b ≠ 0 := by
      rw [SS]; intro hh
      have h1 : (0:ℝ) < (2-b)^2 + b^2 := by positivity
      linarith
    have hb2 : b^2 ≠ 0 := pow_ne_zero 2 hb
    have hb4 : b^4 ≠ 0 := pow_ne_zero 4 hb
    have hb6 : b^6 ≠ 0 := pow_ne_zero 6 hb
    simp only [stuff2f, K2pf, s2C0, s2C1, s2C2, s2C3, s2D1, s2D2, s2D3, SS]
    field_simp
    ring

noncomputable def dStuff2f (b : ℝ) : ℝ :=
  s2C0*(-(4*b-4))/(SS b)^2
  + s2C1*(-2/b^3) + s2C2*(-4/b^5) + s2C3*(-6/b^7)
  + s2D1*(-2/(b^3*SS b) - (4*b-4)/(b^2*(SS b)^2))
  + s2D2*(-4/(b^5*SS b) - (4*b-4)/(b^4*(SS b)^2))
  + s2D3*(-6/(b^7*SS b) - (4*b-4)/(b^6*(SS b)^2))

noncomputable def d2Stuff2f (b : ℝ) : ℝ :=
  s2C0*((2*(4*b-4)^2 - (SS b)*4)/((SS b)^3))
  + s2C1*(6/b^4) + s2C2*(20/b^6) + s2C3*(42/b^8)
  + s2D1*(6/(b^4*SS b) + 2*1*(4*b-4)/(b^3*(SS b)^2) + (2*(4*b-4)^2 - (SS b)*4)/(b^2*(SS b)^3))
  + s2D2*(20/(b^6*SS b) + 2*2*(4*b-4)/(b^5*(SS b)^2) + (2*(4*b-4)^2 - (SS b)*4)/(b^4*(SS b)^3))
  + s2D3*(42/(b^8*SS b) + 2*3*(4*b-4)/(b^7*(SS b)^2) + (2*(4*b-4)^2 - (SS b)*4)/(b^6*(SS b)^3))

lemma hasDerivAt_stuff2f (b : ℝ) (hb : (0:ℝ) < b) (hS0 : (0:ℝ) < SS b) :
    HasDerivAt stuff2f (dStuff2f b) b := by
  rw [stuff2f_funeq]
  have hc : HasDerivAt (fun _ : ℝ => (1/4:ℝ)) 0 b := hasDerivAt_const b _
  have hSS := hasDerivAt_SS b
  have h1 : HasDerivAt (fun t : ℝ => s2C0/SS t) (s2C0*(-(4*b-4))/(SS b)^2) b := by
    have h0 : HasDerivAt (fun _ : ℝ => s2C0) 0 b := hasDerivAt_const b s2C0
    refine (h0.div hSS hS0.ne').congr_deriv ?_
    have e : (0:ℝ) < (SS b)^2 := by positivity
    field_simp
    ring
  have h2 : HasDerivAt (fun t : ℝ => s2C1/t^2) (s2C1*(-2/b^3)) b := by
    have h0 : HasDerivAt (fun _ : ℝ => s2C1) 0 b := hasDerivAt_const b s2C1
    have hd : HasDerivAt (fun t : ℝ => t^2) (2*b) b := by simpa using hasDerivAt_pow 2 b
    refine (h0.div hd (by positivity)).congr_deriv ?_
    have e : (0:ℝ) < (b^2)^2 := by positivity
    field_simp
    ring
  have h3 : HasDerivAt (fun t : ℝ => s2C2/t^4) (s2C2*(-4/b^5)) b := by
    have h0 : HasDerivAt (fun _ : ℝ => s2C2) 0 b := hasDerivAt_const b s2C2
    have hd : HasDerivAt (fun t : ℝ => t^4) (4*b^3) b := by simpa using hasDerivAt_pow 4 b
    refine (h0.div hd (by positivity)).congr_deriv ?_
    have e : (0:ℝ) < (b^4)^2 := by positivity
    field_simp
    ring
  have h4 : HasDerivAt (fun t : ℝ => s2C3/t^6) (s2C3*(-6/b^7)) b := by
    have h0 : HasDerivAt (fun _ : ℝ => s2C3) 0 b := hasDerivAt_const b s2C3
    have hd : HasDerivAt (fun t : ℝ => t^6) (6*b^5) b := by simpa using hasDerivAt_pow 6 b
    refine (h0.div hd (by positivity)).congr_deriv ?_
    have e : (0:ℝ) < (b^6)^2 := by positivity
    field_simp
    ring
  have h5 : HasDerivAt (fun t : ℝ => s2D1/(t^2*SS t))
      (s2D1*(-2/(b^3*SS b) - (4*b-4)/(b^2*(SS b)^2))) b := by
    have h0 : HasDerivAt (fun _ : ℝ => s2D1) 0 b := hasDerivAt_const b s2D1
    have hd1 : HasDerivAt (fun t : ℝ => t^2) (2*b) b := by simpa using hasDerivAt_pow 2 b
    have hd := hd1.mul hSS
    refine (h0.div hd (by simp only [Pi.mul_apply]; exact mul_ne_zero (pow_ne_zero 2 hb.ne') hS0.ne')).congr_deriv ?_
    have e : (0:ℝ) < (b^2*SS b)^2 := by positivity
    simp only [Pi.mul_apply]
    field_simp
    ring
  have h6 : HasDerivAt (fun t : ℝ => s2D2/(t^4*SS t))
      (s2D2*(-4/(b^5*SS b) - (4*b-4)/(b^4*(SS b)^2))) b := by
    have h0 : HasDerivAt (fun _ : ℝ => s2D2) 0 b := hasDerivAt_const b s2D2
    have hd1 : HasDerivAt (fun t : ℝ => t^4) (4*b^3) b := by simpa using hasDerivAt_pow 4 b
    have hd := hd1.mul hSS
    refine (h0.div hd (by simp only [Pi.mul_apply]; exact mul_ne_zero (pow_ne_zero 4 hb.ne') hS0.ne')).congr_deriv ?_
    have e : (0:ℝ) < (b^4*SS b)^2 := by positivity
    simp only [Pi.mul_apply]
    field_simp
    ring
  have h7 : HasDerivAt (fun t : ℝ => s2D3/(t^6*SS t))
      (s2D3*(-6/(b^7*SS b) - (4*b-4)/(b^6*(SS b)^2))) b := by
    have h0 : HasDerivAt (fun _ : ℝ => s2D3) 0 b := hasDerivAt_const b s2D3
    have hd1 : HasDerivAt (fun t : ℝ => t^6) (6*b^5) b := by simpa using hasDerivAt_pow 6 b
    have hd := hd1.mul hSS
    refine (h0.div hd (by simp only [Pi.mul_apply]; exact mul_ne_zero (pow_ne_zero 6 hb.ne') hS0.ne')).congr_deriv ?_
    have e : (0:ℝ) < (b^6*SS b)^2 := by positivity
    simp only [Pi.mul_apply]
    field_simp
    ring
  have hsum := ((((((hc.add h1).add h2).add h3).add h4).add h5).add h6).add h7
  have hfun : (fun b : ℝ => 1/4 + s2C0/SS b + s2C1/b^2 + s2C2/b^4 + s2C3/b^6
      + s2D1/(b^2*SS b) + s2D2/(b^4*SS b) + s2D3/(b^6*SS b))
      = (((((((fun _ : ℝ => (1/4:ℝ)) + fun t : ℝ => s2C0/SS t) + fun t : ℝ => s2C1/t^2)
        + fun t : ℝ => s2C2/t^4) + fun t : ℝ => s2C3/t^6) + fun t : ℝ => s2D1/(t^2*SS t))
        + fun t : ℝ => s2D2/(t^4*SS t)) + fun t : ℝ => s2D3/(t^6*SS t) := by
    funext t; simp only [Pi.add_apply]; try ring
  rw [hfun]
  have hv : (0:ℝ) + s2C0*(-(4*b-4))/(SS b)^2 + s2C1*(-2/b^3) + s2C2*(-4/b^5) + s2C3*(-6/b^7)
      + s2D1*(-2/(b^3*SS b) - (4*b-4)/(b^2*(SS b)^2))
      + s2D2*(-4/(b^5*SS b) - (4*b-4)/(b^4*(SS b)^2))
      + s2D3*(-6/(b^7*SS b) - (4*b-4)/(b^6*(SS b)^2)) = dStuff2f b := by
    simp only [dStuff2f]
    ring
  exact hsum.congr_deriv hv





set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## Positivity helpers -/
lemma Q1pos (b : ℝ) : 0 < 8*b^2-24*b+19 := by nlinarith [sq_nonneg (b - 3/2)]
lemma Q2pos (b : ℝ) : 0 < 8*(1+b)^2+1 := by positivity
lemma Q3pos (b : ℝ) : 0 < 8*(2-b)^2+1 := by positivity
lemma Spos {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) : 0 < (2-b)^2+b^2 := by nlinarith [sq_nonneg (2-b), sq_nonneg b, h1]
lemma bpos {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) : 0 < b := by linarith


/-! ## Derivatives of `I0f`, `J0f` -/
noncomputable def dI0f (b : ℝ) : ℝ := (-7)/(384*(2-b)^3)
noncomputable def d2I0f (b : ℝ) : ℝ := (-7)/(128*(2-b)^4)
noncomputable def dJ0f (b : ℝ) : ℝ := 7*(4*b-4)/(384*((2-b)^2+b^2)^2)
noncomputable def d2J0f (b : ℝ) : ℝ := 7*((2-b)^2+b^2 - 8*(b-1)^2)/(96*((2-b)^2+b^2)^3)

lemma hasDerivAt_SS_new (b : ℝ) : HasDerivAt (fun t : ℝ => (2-t)^2+t^2) (4*b-4) b := by
  have h1 : HasDerivAt (fun t : ℝ => (2-t)^2) (2*b-4) b := by
    have := hasDerivAt_2ms2 b; refine this.congr_deriv ?_; ring
  have h2 : HasDerivAt (fun t : ℝ => t^2) (2*b) b := by simpa using hasDerivAt_pow 2 b
  refine (h1.add h2).congr_deriv ?_; ring

lemma hasDerivAt_I0f (b : ℝ) (h : (0:ℝ) < 2-b) : HasDerivAt I0f (dI0f b) b := by
  have h1 : HasDerivAt (fun t : ℝ => (2-t)^2) (2*b-4) b := by
    have hh := hasDerivAt_2ms2 b; refine hh.congr_deriv ?_; ring
  have h2 : HasDerivAt (fun t : ℝ => 7/(768*((2-t)^2))) (-7*(2*b-4)/(768*((2-b)^2)^2)) b := by
    have h0 : HasDerivAt (fun _ : ℝ => (7:ℝ)) 0 b := hasDerivAt_const b 7
    have hd : HasDerivAt (fun t : ℝ => 768*(2-t)^2) (768*(2*b-4)) b := h1.const_mul 768
    refine (h0.div hd (by positivity)).congr_deriv ?_
    have e : (0:ℝ) < (768*((2-b)^2))^2 := by positivity
    field_simp
    ring
  have hc : HasDerivAt (fun _ : ℝ => (1/4:ℝ)) 0 b := hasDerivAt_const b _
  have hval : (0:ℝ) - (-7*(2*b-4)/(768*((2-b)^2)^2)) = dI0f b := by
    simp only [dI0f]; field_simp; ring
  have hres := (hc.sub h2).congr_deriv hval
  have hfun : ((fun x : ℝ => (1/4:ℝ)) - fun t : ℝ => 7/(768*((2-t)^2)))
      = fun β : ℝ => 1/4 - 7/(768*((2-β)^2)) := by
    funext t; simp only [Pi.sub_apply]
  unfold I0f
  rw [hfun] at hres
  exact hres

lemma hasDerivAt_dI0f (b : ℝ) (h : (0:ℝ) < 2-b) : HasDerivAt dI0f (d2I0f b) b := by
  have h1 : HasDerivAt (fun t : ℝ => (2-t)^3) (-3*b^2+12*b-12) b := by
    have hh := hasDerivAt_2ms3 b; refine hh.congr_deriv ?_; ring
  have h2 : HasDerivAt (fun t : ℝ => 384*((2-t)^3)) (384*(-3*b^2+12*b-12)) b := h1.const_mul 384
  have h0 : HasDerivAt (fun _ : ℝ => (-7:ℝ)) 0 b := hasDerivAt_const b (-7)
  have hval : (0 * (384*((2-b)^3)) - (-7) * (384*(-3*b^2+12*b-12)))/(384*((2-b)^3))^2 = d2I0f b := by
    simp only [d2I0f]; field_simp; ring
  exact (h0.div h2 (by positivity)).congr_deriv hval

lemma hasDerivAt_J0f (b : ℝ) (h : (0:ℝ) < (2-b)^2+b^2) : HasDerivAt J0f (dJ0f b) b := by
  have hS := hasDerivAt_SS_new b
  have h0 : HasDerivAt (fun _ : ℝ => (-7:ℝ)) 0 b := hasDerivAt_const b (-7)
  have hden : HasDerivAt (fun t : ℝ => 384*((2-t)^2+t^2)) (384*(4*b-4)) b := hS.const_mul 384
  have hval : (0 * (384*((2-b)^2+b^2)) - (-7) * (384*(4*b-4)))/(384*((2-b)^2+b^2))^2 = dJ0f b := by
    simp only [dJ0f]; field_simp; ring
  have hq := (h0.div hden (by positivity)).congr_deriv hval
  have hc : HasDerivAt (fun _ : ℝ => (1/4:ℝ)) 0 b := hasDerivAt_const b _
  have hsum := hc.add hq
  have hfun : ((fun _ : ℝ => (1/4:ℝ)) + (fun x : ℝ => (-7:ℝ))/(fun t : ℝ => 384*((2-t)^2+t^2)))
      = fun β : ℝ => 1/4 - 7/(384*((2-β)^2+β^2)) := by
    funext t; simp only [Pi.add_apply, Pi.div_apply]; ring
  unfold J0f
  rw [hfun] at hsum
  simpa using hsum

lemma hasDerivAt_dJ0f (b : ℝ) (h : (0:ℝ) < (2-b)^2+b^2) : HasDerivAt dJ0f (d2J0f b) b := by
  have hS := hasDerivAt_SS_new b
  have hnum : HasDerivAt (fun t : ℝ => 7*(4*t-4)) (28:ℝ) b := by
    have h1 : HasDerivAt (fun t : ℝ => 4*t-4) 4 b := by
      simpa using ((hasDerivAt_id b).const_mul (4:ℝ)).sub_const 4
    have := h1.const_mul 7
    refine this.congr_deriv ?_; ring
  have hden : HasDerivAt (fun t : ℝ => 384*(((2-t)^2+t^2)^2)) (384*(2*((2-b)^2+b^2)*(4*b-4))) b := by
    have hsq : HasDerivAt (fun y : ℝ => y^2) (2*((2-b)^2+b^2)) ((2-b)^2+b^2) := by
      simpa using hasDerivAt_pow 2 ((2-b)^2+b^2)
    have hcomp := hsq.comp b hS
    have hcomp' : HasDerivAt (fun t : ℝ => ((2-t)^2+t^2)^2) (2*((2-b)^2+b^2)*(4*b-4)) b :=
      hcomp.congr_deriv (by ring)
    exact hcomp'.const_mul 384
  have hval : (28 * (384*(((2-b)^2+b^2)^2)) - 7*(4*b-4) * (384*(2*((2-b)^2+b^2)*(4*b-4))))/(384*(((2-b)^2+b^2)^2))^2 = d2J0f b := by
    simp only [d2J0f]; field_simp; ring
  exact (hnum.div hden (by positivity)).congr_deriv hval

/-- `dStuff1f` as a single fraction. -/
lemma dStuff1f_eq (b : ℝ) (h : (0:ℝ) < 2-b) :
    dStuff1f b = (2*s1c1*(2-b)^6 + 4*s1c2*(2-b)^4 + 6*s1c3*(2-b)^2 + 8*s1c4)/(2-b)^9 := by
  simp only [dStuff1f]
  field_simp

lemma dd1_le {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : dd1 b ≤ (1/2) := by
  have hid : dd1 b = (2*(8*b^2-24*b+17))/((8*b^2-24*b+19)^2) := by simp only [dd1] <;> ring
  have hQ : (0:ℝ) < 8*b^2-24*b+19 := Q1pos b
  have hden : (0:ℝ) < (8*b^2-24*b+19)^2 := by positivity
  have hu : (0:ℝ) ≤ 1-b := by linarith
  rw [hid, div_le_iff₀ hden]
  have hcert : (0:ℝ) ≤ ((1/2))*((8*b^2-24*b+19)^2) - (2*(8*b^2-24*b+17)) := by
    have hh : ((1/2))*((8*b^2-24*b+19)^2) - (2*(8*b^2-24*b+17)) = (32)*(1-b)^4 + (64)*(1-b)^3 + (40)*(1-b)^2 + (8)*(1-b)^1 + (5/2) := by ring
    rw [hh]; positivity
  linarith

lemma d2d1_ge {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : (-3/5) ≤ d2d1 b := by
  have hid : d2d1 b = (2*(16*b-24)*(4-(8*b^2-24*b+19)))/((8*b^2-24*b+19)^3) := by simp only [d2d1] <;> ring
  have hQ : (0:ℝ) < 8*b^2-24*b+19 := Q1pos b
  have hden : (0:ℝ) < (8*b^2-24*b+19)^3 := by positivity
  have hu : (0:ℝ) ≤ 1-b := by linarith
  rw [hid, le_div_iff₀ hden]
  have hcert : (0:ℝ) ≤ (2*(16*b-24)*(4-(8*b^2-24*b+19))) - ((-3/5))*((8*b^2-24*b+19)^3) := by
    have hh : (2*(16*b-24)*(4-(8*b^2-24*b+19))) - ((-3/5))*((8*b^2-24*b+19)^3) = ((1536/5))*(1-b)^6 + ((4608/5))*(1-b)^5 + ((6336/5))*(1-b)^4 + ((6272/5))*(1-b)^3 + ((4296/5))*(1-b)^2 + ((1128/5))*(1-b)^1 + (1/5) := by ring
    rw [hh]; positivity
  linarith

lemma dd2_le {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : dd2 b ≤ 0 := by
  have hid : dd2 b = (-2*(8*(1+b)^2-1))/((8*(1+b)^2+1)^2) := by simp only [dd2] <;> ring
  have hb1 : (0:ℝ) < 2-b := by linarith
  have hb2 : (0:ℝ) ≤ 1-b := by linarith
  have hb3 : (0:ℝ) < b := by linarith
  have hden : (0:ℝ) < (8*(1+b)^2+1)^2 := by positivity
  have hv : (0:ℝ) ≤ b-1/2 := by linarith
  rw [hid, div_le_iff₀ hden]
  have hcert : (0:ℝ) ≤ (0)*((8*(1+b)^2+1)^2) - (-2*(8*(1+b)^2-1)) := by
    have hh : (0)*((8*(1+b)^2+1)^2) - (-2*(8*(1+b)^2-1)) = (16)*(b-1/2)^2 + (48)*(b-1/2)^1 + 34 := by ring
    rw [hh]; positivity
  linarith

lemma dd2_ge {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : (-1/8) ≤ dd2 b := by
  have hid : dd2 b = (-2*(8*(1+b)^2-1))/((8*(1+b)^2+1)^2) := by simp only [dd2] <;> ring
  have hb1 : (0:ℝ) < 2-b := by linarith
  have hb2 : (0:ℝ) ≤ 1-b := by linarith
  have hb3 : (0:ℝ) < b := by linarith
  have hden : (0:ℝ) < (8*(1+b)^2+1)^2 := by positivity
  have hv : (0:ℝ) ≤ b-1/2 := by linarith
  rw [hid, le_div_iff₀ hden]
  have hcert : (0:ℝ) ≤ (-2*(8*(1+b)^2-1)) - ((-1/8))*((8*(1+b)^2+1)^2) := by
    have hh : (-2*(8*(1+b)^2-1)) - ((-1/8))*((8*(1+b)^2+1)^2) = (8)*(b-1/2)^4 + (48)*(b-1/2)^3 + (94)*(b-1/2)^2 + (66)*(b-1/2)^1 + (89/8) := by ring
    rw [hh]; positivity
  linarith

lemma d2d2_ge {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : 0 ≤ d2d2 b := by
  have hid : d2d2 b = (32*(1+b)*(8*(1+b)^2-3))/((8*(1+b)^2+1)^3) := by simp only [d2d2] <;> ring
  have hb1 : (0:ℝ) < 2-b := by linarith
  have hb2 : (0:ℝ) ≤ 1-b := by linarith
  have hb3 : (0:ℝ) < b := by linarith
  have hden : (0:ℝ) < (8*(1+b)^2+1)^3 := by positivity
  have hv : (0:ℝ) ≤ b-1/2 := by linarith
  rw [hid, le_div_iff₀ hden]
  have hcert : (0:ℝ) ≤ (32*(1+b)*(8*(1+b)^2-3)) - (0)*((8*(1+b)^2+1)^3) := by
    have hh : (32*(1+b)*(8*(1+b)^2-3)) - (0)*((8*(1+b)^2+1)^3) = (256)*(b-1/2)^3 + (1152)*(b-1/2)^2 + (1632)*(b-1/2)^1 + 720 := by ring
    rw [hh]; positivity
  linarith

lemma ddr_le {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : ddr b ≤ (1/2) := by
  have hid : ddr b = (2*(8*(2-b)^2-1))/((8*(2-b)^2+1)^2) := by simp only [ddr] <;> ring
  have hb1 : (0:ℝ) < 2-b := by linarith
  have hb2 : (0:ℝ) ≤ 1-b := by linarith
  have hb3 : (0:ℝ) < b := by linarith
  have hden : (0:ℝ) < (8*(2-b)^2+1)^2 := by positivity
  have hu : (0:ℝ) ≤ 1-b := by linarith
  rw [hid, div_le_iff₀ hden]
  have hcert : (0:ℝ) ≤ ((1/2))*((8*(2-b)^2+1)^2) - (2*(8*(2-b)^2-1)) := by
    have hh : ((1/2))*((8*(2-b)^2+1)^2) - (2*(8*(2-b)^2-1)) = (32)*(1-b)^4 + (128)*(1-b)^3 + (184)*(1-b)^2 + (112)*(1-b)^1 + (53/2) := by ring
    rw [hh]; positivity
  linarith

lemma ddr_ge {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : 0 ≤ ddr b := by
  have hid : ddr b = (2*(8*(2-b)^2-1))/((8*(2-b)^2+1)^2) := by simp only [ddr] <;> ring
  have hb1 : (0:ℝ) < 2-b := by linarith
  have hb2 : (0:ℝ) ≤ 1-b := by linarith
  have hb3 : (0:ℝ) < b := by linarith
  have hden : (0:ℝ) < (8*(2-b)^2+1)^2 := by positivity
  have hu : (0:ℝ) ≤ 1-b := by linarith
  rw [hid, le_div_iff₀ hden]
  have hcert : (0:ℝ) ≤ (2*(8*(2-b)^2-1)) - (0)*((8*(2-b)^2+1)^2) := by
    have hh : (2*(8*(2-b)^2-1)) - (0)*((8*(2-b)^2+1)^2) = (16)*(1-b)^2 + (32)*(1-b)^1 + 14 := by ring
    rw [hh]; positivity
  linarith

lemma d2dr_ge {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : 0 ≤ d2dr b := by
  have hid : d2dr b = (32*(2-b)*(8*(2-b)^2-3))/((8*(2-b)^2+1)^3) := by simp only [d2dr] <;> ring
  have hb1 : (0:ℝ) < 2-b := by linarith
  have hb2 : (0:ℝ) ≤ 1-b := by linarith
  have hb3 : (0:ℝ) < b := by linarith
  have hden : (0:ℝ) < (8*(2-b)^2+1)^3 := by positivity
  have hu : (0:ℝ) ≤ 1-b := by linarith
  rw [hid, le_div_iff₀ hden]
  have hcert : (0:ℝ) ≤ (32*(2-b)*(8*(2-b)^2-3)) - (0)*((8*(2-b)^2+1)^3) := by
    have hh : (32*(2-b)*(8*(2-b)^2-3)) - (0)*((8*(2-b)^2+1)^3) = (256)*(1-b)^3 + (768)*(1-b)^2 + (672)*(1-b)^1 + 160 := by ring
    rw [hh]; positivity
  linarith

lemma dI0f_le {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : dI0f b ≤ 0 := by
  have hid : dI0f b = (-7)/(384*(2-b)^3) := by simp only [dI0f] <;> ring
  have hb1 : (0:ℝ) < 2-b := by linarith
  have hb2 : (0:ℝ) ≤ 1-b := by linarith
  have hb3 : (0:ℝ) < b := by linarith
  have hden : (0:ℝ) < 384*(2-b)^3 := by positivity
  rw [hid, div_le_iff₀ hden]
  have hcert : (0:ℝ) ≤ (0)*(384*(2-b)^3) - (-7) := by
    have hh : (0)*(384*(2-b)^3) - (-7) = 7 := by ring
    rw [hh]; positivity
  linarith

lemma dI0f_ge {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : (-7/384) ≤ dI0f b := by
  have hid : dI0f b = (-7)/(384*(2-b)^3) := by simp only [dI0f] <;> ring
  have hb1 : (0:ℝ) < 2-b := by linarith
  have hb2 : (0:ℝ) ≤ 1-b := by linarith
  have hb3 : (0:ℝ) < b := by linarith
  have hden : (0:ℝ) < 384*(2-b)^3 := by positivity
  have hu : (0:ℝ) ≤ 1-b := by linarith
  rw [hid, le_div_iff₀ hden]
  have hcert : (0:ℝ) ≤ (-7) - ((-7/384))*(384*(2-b)^3) := by
    have hh : (-7) - ((-7/384))*(384*(2-b)^3) = (7)*(1-b)^3 + (21)*(1-b)^2 + (21)*(1-b)^1 := by ring
    rw [hh]; positivity
  linarith

lemma d2I0f_le {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : d2I0f b ≤ 0 := by
  have hid : d2I0f b = (-7)/(128*(2-b)^4) := by simp only [d2I0f] <;> ring
  have hb1 : (0:ℝ) < 2-b := by linarith
  have hb2 : (0:ℝ) ≤ 1-b := by linarith
  have hb3 : (0:ℝ) < b := by linarith
  have hden : (0:ℝ) < 128*(2-b)^4 := by positivity
  rw [hid, div_le_iff₀ hden]
  have hcert : (0:ℝ) ≤ (0)*(128*(2-b)^4) - (-7) := by
    have hh : (0)*(128*(2-b)^4) - (-7) = 7 := by ring
    rw [hh]; positivity
  linarith

lemma d2I0f_ge {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : (-7/128) ≤ d2I0f b := by
  have hid : d2I0f b = (-7)/(128*(2-b)^4) := by simp only [d2I0f] <;> ring
  have hb1 : (0:ℝ) < 2-b := by linarith
  have hb2 : (0:ℝ) ≤ 1-b := by linarith
  have hb3 : (0:ℝ) < b := by linarith
  have hden : (0:ℝ) < 128*(2-b)^4 := by positivity
  have hu : (0:ℝ) ≤ 1-b := by linarith
  rw [hid, le_div_iff₀ hden]
  have hcert : (0:ℝ) ≤ (-7) - ((-7/128))*(128*(2-b)^4) := by
    have hh : (-7) - ((-7/128))*(128*(2-b)^4) = (7)*(1-b)^4 + (28)*(1-b)^3 + (42)*(1-b)^2 + (28)*(1-b)^1 := by ring
    rw [hh]; positivity
  linarith

lemma dJ0f_le {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : dJ0f b ≤ 0 := by
  have hid : dJ0f b = (7*(4*b-4))/(384*((2-b)^2+b^2)^2) := by simp only [dJ0f] <;> ring
  have hb1 : (0:ℝ) < 2-b := by linarith
  have hb2 : (0:ℝ) ≤ 1-b := by linarith
  have hb3 : (0:ℝ) < b := by linarith
  have hden : (0:ℝ) < 384*((2-b)^2+b^2)^2 := by positivity
  have hu : (0:ℝ) ≤ 1-b := by linarith
  rw [hid, div_le_iff₀ hden]
  have hcert : (0:ℝ) ≤ (0)*(384*((2-b)^2+b^2)^2) - (7*(4*b-4)) := by
    have hh : (0)*(384*((2-b)^2+b^2)^2) - (7*(4*b-4)) = (28)*(1-b)^1 := by ring
    rw [hh]; positivity
  linarith

lemma dJ0f_ge {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : (-7/768) ≤ dJ0f b := by
  have hid : dJ0f b = (7*(4*b-4))/(384*((2-b)^2+b^2)^2) := by simp only [dJ0f] <;> ring
  have hb1 : (0:ℝ) < 2-b := by linarith
  have hb2 : (0:ℝ) ≤ 1-b := by linarith
  have hb3 : (0:ℝ) < b := by linarith
  have hden : (0:ℝ) < 384*((2-b)^2+b^2)^2 := by positivity
  have hu : (0:ℝ) ≤ 1-b := by linarith
  have hv : (0:ℝ) ≤ b-1/2 := by linarith
  rw [hid, le_div_iff₀ hden]
  have hcert : (0:ℝ) ≤ (7*(4*b-4)) - ((-7/768))*(384*((2-b)^2+b^2)^2) := by
    have hh : (7*(4*b-4)) - ((-7/768))*(384*((2-b)^2+b^2)^2) = 224*(b-1/2)^4 + 672*(1-b)^1*(b-1/2)^3 + 784*(1-b)^2*(b-1/2)^2 + 448*(1-b)^3*(b-1/2)^1 + 126*(1-b)^4 := by ring
    rw [hh]; positivity
  linarith

lemma d2J0f_ge {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : 0 ≤ d2J0f b := by
  have hid : d2J0f b = (7*((2-b)^2+b^2 - 8*(b-1)^2))/(96*((2-b)^2+b^2)^3) := by simp only [d2J0f] <;> ring
  have hb1 : (0:ℝ) < 2-b := by linarith
  have hb2 : (0:ℝ) ≤ 1-b := by linarith
  have hb3 : (0:ℝ) < b := by linarith
  have hden : (0:ℝ) < 96*((2-b)^2+b^2)^3 := by positivity
  have hu : (0:ℝ) ≤ 1-b := by linarith
  have hv : (0:ℝ) ≤ b-1/2 := by linarith
  rw [hid, le_div_iff₀ hden]
  have hcert : (0:ℝ) ≤ (7*((2-b)^2+b^2 - 8*(b-1)^2)) - (0)*(96*((2-b)^2+b^2)^3) := by
    have hh : (7*((2-b)^2+b^2 - 8*(b-1)^2)) - (0)*(96*((2-b)^2+b^2)^3) = 56*(b-1/2)^2 + 112*(1-b)^1*(b-1/2)^1 + 14*(1-b)^2 := by ring
    rw [hh]; positivity
  linarith

lemma d2J0f_le {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : d2J0f b ≤ (7/384) := by
  have hid : d2J0f b = (7*((2-b)^2+b^2 - 8*(b-1)^2))/(96*((2-b)^2+b^2)^3) := by simp only [d2J0f] <;> ring
  have hb1 : (0:ℝ) < 2-b := by linarith
  have hb2 : (0:ℝ) ≤ 1-b := by linarith
  have hb3 : (0:ℝ) < b := by linarith
  have hden : (0:ℝ) < 96*((2-b)^2+b^2)^3 := by positivity
  have hu : (0:ℝ) ≤ 1-b := by linarith
  rw [hid, div_le_iff₀ hden]
  have hcert : (0:ℝ) ≤ ((7/384))*(96*((2-b)^2+b^2)^3) - (7*((2-b)^2+b^2 - 8*(b-1)^2)) := by
    have hh : ((7/384))*(96*((2-b)^2+b^2)^3) - (7*((2-b)^2+b^2 - 8*(b-1)^2)) = (14)*(1-b)^6 + (42)*(1-b)^4 + (84)*(1-b)^2 := by ring
    rw [hh]; positivity
  linarith

lemma dStuff1f_le {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : dStuff1f b ≤ (1/8) := by
  have hid : dStuff1f b = (2*s1c1*(2-b)^6 + 4*s1c2*(2-b)^4 + 6*s1c3*(2-b)^2 + 8*s1c4)/((2-b)^9) := by rw [dStuff1f_eq b (by linarith : (0:ℝ) < 2-b)]
  have hb1 : (0:ℝ) < 2-b := by linarith
  have hb2 : (0:ℝ) ≤ 1-b := by linarith
  have hb3 : (0:ℝ) < b := by linarith
  have hden : (0:ℝ) < (2-b)^9 := by positivity
  have hu : (0:ℝ) ≤ 1-b := by linarith
  rw [hid, div_le_iff₀ hden]
  have hcert : (0:ℝ) ≤ ((1/8))*((2-b)^9) - (2*s1c1*(2-b)^6 + 4*s1c2*(2-b)^4 + 6*s1c3*(2-b)^2 + 8*s1c4) := by
    have hh : ((1/8))*((2-b)^9) - (2*s1c1*(2-b)^6 + 4*s1c2*(2-b)^4 + 6*s1c3*(2-b)^2 + 8*s1c4) = ((1/8))*(1-b)^9 + ((9/8))*(1-b)^8 + ((9/2))*(1-b)^7 + ((60472383246227/5760000000000))*(1-b)^6 + ((15112383246227/960000000000))*(1-b)^5 + ((6041255121227/384000000000))*(1-b)^4 + ((3018998871227/288000000000))*(1-b)^3 + ((193265102874299/43008000000000))*(1-b)^2 + ((121064820061799/107520000000000))*(1-b)^1 + (1948735644373801/15482880000000000) := by simp only [s1c1, s1c2, s1c3, s1c4, l2lo]; ring
    rw [hh]; positivity
  linarith

lemma dStuff1f_ge {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : (-1/8) ≤ dStuff1f b := by
  have hid : dStuff1f b = (2*s1c1*(2-b)^6 + 4*s1c2*(2-b)^4 + 6*s1c3*(2-b)^2 + 8*s1c4)/((2-b)^9) := by rw [dStuff1f_eq b (by linarith : (0:ℝ) < 2-b)]
  have hb1 : (0:ℝ) < 2-b := by linarith
  have hb2 : (0:ℝ) ≤ 1-b := by linarith
  have hb3 : (0:ℝ) < b := by linarith
  have hden : (0:ℝ) < (2-b)^9 := by positivity
  have hu : (0:ℝ) ≤ 1-b := by linarith
  rw [hid, le_div_iff₀ hden]
  have hcert : (0:ℝ) ≤ (2*s1c1*(2-b)^6 + 4*s1c2*(2-b)^4 + 6*s1c3*(2-b)^2 + 8*s1c4) - ((-1/8))*((2-b)^9) := by
    have hh : (2*s1c1*(2-b)^6 + 4*s1c2*(2-b)^4 + 6*s1c3*(2-b)^2 + 8*s1c4) - ((-1/8))*((2-b)^9) = ((1/8))*(1-b)^9 + ((9/8))*(1-b)^8 + ((9/2))*(1-b)^7 + ((60487616753773/5760000000000))*(1-b)^6 + ((15127616753773/960000000000))*(1-b)^5 + ((6054744878773/384000000000))*(1-b)^4 + ((3029001128773/288000000000))*(1-b)^3 + ((193806897125701/43008000000000))*(1-b)^2 + ((120855179938201/107520000000000))*(1-b)^1 + (1921984355626199/15482880000000000) := by simp only [s1c1, s1c2, s1c3, s1c4, l2lo]; ring
    rw [hh]; positivity
  linarith



/-! ## Bounds on `psi7`, `dpsi7`, `d2psi7` and the ranges of `dl1`,`dl2`,`dlr` -/

lemma psi7_le_self {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : psi7 x ≤ x := by
  have h : 0 ≤ 1/3 - x^2/5 + x^4/7 := by nlinarith [sq_nonneg (x^2 - 7/10), sq_nonneg x, hx0, hx1]
  have h' : 0 ≤ x^3*(1/3 - x^2/5 + x^4/7) := mul_nonneg (pow_nonneg hx0 3) h
  rw [psi7]; nlinarith [h']

lemma psi7_range {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ psi7 x ∧ psi7 x ≤ 1 := by
  have h0 : 0 ≤ psi7 x := by
    have h1 : 0 ≤ x*(1 - x^2/3) := mul_nonneg hx0 (by nlinarith)
    have h2 : 0 ≤ x^5*(1/5 - x^2/7) :=
      mul_nonneg (pow_nonneg hx0 5) (by nlinarith [sq_nonneg x, hx0, hx1])
    have he : psi7 x = x*(1 - x^2/3) + x^5*(1/5 - x^2/7) := by rw [psi7]; ring
    rw [he]; linarith
  exact ⟨h0, le_trans (psi7_le_self hx0 hx1) hx1⟩

lemma abs_dpsi7_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : |dpsi7 x| ≤ 1 := by
  rw [abs_of_nonneg (dpsi7_nonneg hx0 hx1)]
  exact dpsi7_le_one x

lemma d2psi7_le_zero {x : ℝ} (hx : 0 ≤ x) : d2psi7 x ≤ 0 := by
  have h : 0 ≤ 3*x^4 - 2*x^2 + 1 := by nlinarith [sq_nonneg (x^2 - 1/3)]
  have h2 : 0 ≤ 2*x*(3*x^4 - 2*x^2 + 1) := mul_nonneg (by linarith) h
  rw [d2psi7]
  nlinarith [h2]

lemma d2psi7_ge {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) : -2 ≤ d2psi7 x := by
  have h5 : x^5 ≤ (1/2:ℝ)^5 := pow_le_pow_left₀ hx0 hx1 5
  have h3 : (0:ℝ) ≤ 4*x^3 := by positivity
  rw [d2psi7]
  linarith

lemma abs_d2psi7_le_two {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) : |d2psi7 x| ≤ 2 := by
  rw [abs_le]
  exact ⟨d2psi7_ge hx0 hx1, le_trans (d2psi7_le_zero hx0) (by norm_num)⟩

lemma dl1_range {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : 0 ≤ dl1 b ∧ dl1 b ≤ 1/2 := by
  have hQ : 0 < 8*b^2-24*b+19 := Q1pos b
  constructor
  · rw [dl1]; apply div_nonneg _ hQ.le; linarith
  · rw [dl1, div_le_iff₀ hQ]; nlinarith

lemma dl2_range {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : 0 ≤ dl2 b ∧ dl2 b ≤ 1/2 := by
  have hQ : 0 < 8*(1+b)^2+1 := Q2pos b
  constructor
  · rw [dl2]; apply div_nonneg _ hQ.le; linarith
  · rw [dl2, div_le_iff₀ hQ]; nlinarith [sq_nonneg (1+b)]

lemma dlr_range {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : 0 ≤ dlr b ∧ dlr b ≤ 1/2 := by
  have hQ : 0 < 8*(2-b)^2+1 := Q3pos b
  constructor
  · rw [dlr]; apply div_nonneg _ hQ.le; linarith
  · rw [dlr, div_le_iff₀ hQ]; nlinarith [sq_nonneg (2-b)]

lemma Ctot_bounds {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : 0 ≤ Ctot b ∧ Ctot b ≤ 2 :=
  ⟨Ctot_nonneg h1 h2, Ctot_le h1 h2⟩

lemma two_l2hi_ge {b : ℝ} : (1:ℝ) ≤ 2*l2hi := by simp only [l2hi]; norm_num
lemma l2hi_ge : (1:ℝ) ≤ l2hi + 1/2 := by simp only [l2hi]; norm_num

lemma LAf_bounds2 {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1) : 0 ≤ LAf b ∧ LAf b ≤ 2 := by
  obtain ⟨h2, h3, h4⟩ := LAf_bounds h0 h1
  refine ⟨?_, h2⟩
  rw [LAf]
  have hsum : (∑ k ∈ Finset.range 10, (b/2)^(k+1)/((k:ℝ)+1)) ≤ 1 := by
    have hb : b/2 ≤ 1/2 := by linarith
    have hb0 : 0 ≤ b/2 := by linarith
    have h1' : ∀ k ∈ Finset.range 10, (b/2)^(k+1)/((k:ℝ)+1) ≤ ((1:ℝ)/2)^(k+1) := by
      intro k _
      have hk1 : (b/2)^(k+1) ≤ ((1:ℝ)/2)^(k+1) := pow_le_pow_left₀ hb0 hb (k+1)
      have hk2 : (1:ℝ) ≤ (k:ℝ)+1 := by have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k; linarith
      have hk3 : (0:ℝ) ≤ (b/2)^(k+1) := pow_nonneg hb0 _
      calc (b/2)^(k+1)/((k:ℝ)+1) ≤ (b/2)^(k+1)/1 := div_le_div_of_nonneg_left hk3 one_pos hk2
        _ = (b/2)^(k+1) := by ring
        _ ≤ ((1:ℝ)/2)^(k+1) := hk1
    calc (∑ k ∈ Finset.range 10, (b/2)^(k+1)/((k:ℝ)+1))
        ≤ ∑ k ∈ Finset.range 10, ((1:ℝ)/2)^(k+1) := Finset.sum_le_sum h1'
      _ ≤ 1 := by norm_num [Finset.sum_range_succ]
  linarith [two_l2hi_ge (b := b)]

lemma LBf_bounds2 {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : -2 ≤ LBf b ∧ LBf b ≤ 2 := by
  obtain ⟨h3, h4, h5, h6, h7⟩ := LBf_bounds h1 h2
  refine ⟨?_, h3⟩
  have hl2 : (0:ℝ) ≤ l2hi := by simp only [l2hi]; norm_num
  rw [LBf]
  have hsum : (∑ k ∈ Finset.range 12, (1-b)^(k+1)/((k:ℝ)+1)) ≤ 1 := by
    have hb : 1-b ≤ 1/2 := by linarith
    have hb0 : 0 ≤ 1-b := by linarith
    have h1' : ∀ k ∈ Finset.range 12, (1-b)^(k+1)/((k:ℝ)+1) ≤ ((1:ℝ)/2)^(k+1) := by
      intro k _
      have hk1 : (1-b)^(k+1) ≤ ((1:ℝ)/2)^(k+1) := pow_le_pow_left₀ hb0 hb (k+1)
      have hk2 : (1:ℝ) ≤ (k:ℝ)+1 := by have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k; linarith
      have hk3 : (0:ℝ) ≤ (1-b)^(k+1) := pow_nonneg hb0 _
      calc (1-b)^(k+1)/((k:ℝ)+1) ≤ (1-b)^(k+1)/1 := div_le_div_of_nonneg_left hk3 one_pos hk2
        _ = (1-b)^(k+1) := by ring
        _ ≤ ((1:ℝ)/2)^(k+1) := hk1
    calc (∑ k ∈ Finset.range 12, (1-b)^(k+1)/((k:ℝ)+1))
        ≤ ∑ k ∈ Finset.range 12, ((1:ℝ)/2)^(k+1) := Finset.sum_le_sum h1'
      _ ≤ 1 := by norm_num [Finset.sum_range_succ]
  linarith

lemma dLAf_ge {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1) : -1 ≤ dLAf b := by
  rw [dLAf]
  have hsum : (∑ k ∈ Finset.range 10, (b/2)^k/2) ≤ 1 := by
    have hb : b/2 ≤ 1/2 := by linarith
    have hb0 : 0 ≤ b/2 := by linarith
    have h1' : ∀ k ∈ Finset.range 10, (b/2)^k/2 ≤ ((1:ℝ)/2)^k * (1/2) := by
      intro k _
      have hk : (b/2)^k ≤ ((1:ℝ)/2)^k := pow_le_pow_left₀ hb0 hb k
      have := div_le_div_of_nonneg_right hk (by norm_num : (0:ℝ) ≤ 2)
      simpa [div_eq_mul_inv] using this
    calc (∑ k ∈ Finset.range 10, (b/2)^k/2) ≤ ∑ k ∈ Finset.range 10, ((1:ℝ)/2)^k * (1/2) :=
          Finset.sum_le_sum h1'
      _ ≤ 1 := by norm_num [Finset.sum_range_succ]
  linarith

lemma d2LAf_nonpos {b : ℝ} (h0 : 0 ≤ b) : d2LAf b ≤ 0 := by
  rw [d2LAf]
  have h : ∀ k ∈ Finset.range 10, (0:ℝ) ≤ (k:ℝ)*(b/2)^(k-1)/4 := by
    intro k _
    have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    have hb0 : (0:ℝ) ≤ b/2 := by linarith
    have hk1 : (0:ℝ) ≤ (b/2)^(k-1) := pow_nonneg hb0 _
    positivity
  have := Finset.sum_nonneg h
  linarith

lemma I0f_bounds2 {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : 0 ≤ I0f b ∧ I0f b ≤ 1/4 := by
  have hb : (1:ℝ) ≤ (2-b)^2 := by nlinarith
  constructor
  · rw [I0f]
    have h1' : 7/(768*(2-b)^2) ≤ 7/768 := by
      apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 7) (by norm_num : (0:ℝ) < 768)
      nlinarith
    linarith
  · rw [I0f]; have : 0 ≤ 7/(768*(2-b)^2) := by positivity
    linarith

lemma J0f_bounds2 {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : 0 ≤ J0f b ∧ J0f b ≤ 1/4 := by
  have hS : (1:ℝ) ≤ (2-b)^2+b^2 := by nlinarith [sq_nonneg (2-b), sq_nonneg b, h1]
  constructor
  · rw [J0f]
    have h1' : 7/(384*((2-b)^2+b^2)) ≤ 7/384 := by
      apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 7) (by norm_num : (0:ℝ) < 384)
      nlinarith
    linarith
  · rw [J0f]; have : 0 ≤ 7/(384*((2-b)^2+b^2)) := by positivity
    linarith



/-! ## Polynomial surrogates for `P4r`, `P5r`, `stuff2f` -/

noncomputable def P4poly (b : ℝ) : ℝ :=
  (2747987647/10000000000)*b^5 + (-420012867/500000000)*b^4 + (10380950477/10000000000)*b^3
    + (-3341629571/5000000000)*b^2 + (2080254109/10000000000)*b + (-126736761/10000000000)

noncomputable def P5poly (b : ℝ) : ℝ :=
  (841143/250000000)*b^4 + (185746069/5000000000)*b^3 + (-404667069/5000000000)*b^2
    + (396431701/10000000000)*b + (6764577/10000000000)

noncomputable def S2poly (b : ℝ) : ℝ :=
  (-92469561/250000000)*b^5 + (8147922281/5000000000)*b^4 + (-29269999109/10000000000)*b^3
    + (27261043753/10000000000)*b^2 + (-13573620303/10000000000)*b + (5359007/9765625)

lemma P4poly_le {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : P4poly b ≤ P4r b := by
  have hu : (0:ℝ) ≤ 1-b := by linarith
  have hv : (0:ℝ) ≤ b-1/2 := by linarith
  have hA : (2-b) ≠ 0 := by linarith
  have hb1 : 2*(2-b)^2*((2-b)^2+1/4) ≠ 0 := by positivity
  have hb2 : 2*(2-b)^2*((2-b)^2+1/16) ≠ 0 := by positivity
  have hden : (0:ℝ) < 64*(2-b)^2*((2-b)^2+1/4)*((2-b)^2+1/16) := by positivity
  have hkey : (1/2)/(2*(2-b)^2*((2-b)^2+1/4)) - (1/4)/(2*(2-b)^2*((2-b)^2+1/16))
      = (8*(2-b)^2 - 1)/(64*(2-b)^2*((2-b)^2+1/4)*((2-b)^2+1/16)) := by
    rw [div_sub_div _ _ hb1 hb2]
    field_simp
    ring
  rw [P4r, hkey, show (((2-b)^2-b^2)^2/8) = 2*(1-b)^2 by ring, ← mul_div_assoc]
  rw [le_div_iff₀ hden]
  have hcert : (0:ℝ) ≤ 2*(1-b)^2*(8*(2-b)^2-1)
      - P4poly b * (64*(2-b)^2*((2-b)^2+1/4)*((2-b)^2+1/16)) := by
    have hh : 2*(1-b)^2*(8*(2-b)^2-1)
        - P4poly b * (64*(2-b)^2*((2-b)^2+1/4)*((2-b)^2+1/16)) = (7214868/390625)*(b-1/2)^11 + (419138099/1953125)*(1-b)^1*(b-1/2)^10 + (30397470641/19531250)*(1-b)^2*(b-1/2)^9 + (25095967149/3906250)*(1-b)^3*(b-1/2)^8 + (299352816231/19531250)*(1-b)^4*(b-1/2)^7 + (181485358943/7812500)*(1-b)^5*(b-1/2)^6 + (8148468955499/312500000)*(1-b)^6*(b-1/2)^5 + (15400911533777/625000000)*(1-b)^7*(b-1/2)^4 + (5549092541973/312500000)*(1-b)^8*(b-1/2)^3 + (4657204413087/625000000)*(1-b)^9*(b-1/2)^2 + (434282108679/312500000)*(1-b)^10*(b-1/2)^1 + (11180853377/62500000)*(1-b)^11 := by
      simp only [P4poly]; ring
    rw [hh]; positivity
  linarith

lemma P5poly_le {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : P5poly b ≤ P5r b := by
  have hu : (0:ℝ) ≤ 1-b := by linarith
  have hv : (0:ℝ) ≤ b-1/2 := by linarith
  have hA : (2-b) ≠ 0 := by linarith
  have hA1 : (2-b)^2+1/4 ≠ 0 := by positivity
  have hA2 : (2-b)^2+1/16 ≠ 0 := by positivity
  have hD : (2-b)^4*(4*(2-b)^2+1)^2*(16*(2-b)^2+1)^2 ≠ 0 := by positivity
  have hden : (0:ℝ) < (2-b)^4*(4*(2-b)^2+1)^2*(16*(2-b)^2+1)^2 := by positivity
  have hid : P5r b = ((-2560)*b^9 + (38400)*b^8 + (-253472)*b^7 + (965472)*b^6 + (-2336260)*b^5
        + (3720604)*b^4 + (-3895593)*b^3 + (2583547)*b^2 + (-984119)*b + 163981)
      /((2-b)^4*(4*(2-b)^2+1)^2*(16*(2-b)^2+1)^2) := by
    rw [P5r]; field_simp; ring
  rw [hid, le_div_iff₀ hden]
  have hcert : (0:ℝ) ≤ ((-2560)*b^9 + (38400)*b^8 + (-253472)*b^7 + (965472)*b^6 + (-2336260)*b^5
        + (3720604)*b^4 + (-3895593)*b^3 + (2583547)*b^2 + (-984119)*b + 163981)
      - P5poly b * ((2-b)^4*(4*(2-b)^2+1)^2*(16*(2-b)^2+1)^2) := by
    have hh : ((-2560)*b^9 + (38400)*b^8 + (-253472)*b^7 + (965472)*b^6 + (-2336260)*b^5
        + (3720604)*b^4 + (-3895593)*b^3 + (2583547)*b^2 + (-984119)*b + 163981)
        - P5poly b * ((2-b)^4*(4*(2-b)^2+1)^2*(16*(2-b)^2+1)^2) = (18496036992/390625)*(b-1/2)^16 + (3226974499936/1953125)*(1-b)^1*(b-1/2)^15 + (168337019638112/9765625)*(1-b)^2*(b-1/2)^14 + (925126437836032/9765625)*(1-b)^3*(b-1/2)^13 + (661906290187704/1953125)*(1-b)^4*(b-1/2)^12 + (8886708218474502/9765625)*(1-b)^5*(b-1/2)^11 + (20072148186065238/9765625)*(1-b)^6*(b-1/2)^10 + (8005188448454703/1953125)*(1-b)^7*(b-1/2)^9 + (68061018058959261/9765625)*(1-b)^8*(b-1/2)^8 + (18493579727058144/1953125)*(1-b)^9*(b-1/2)^7 + (95336969787850264/9765625)*(1-b)^10*(b-1/2)^6 + (71970728105610343/9765625)*(1-b)^11*(b-1/2)^5 + (38564166802106649/9765625)*(1-b)^12*(b-1/2)^4 + (14204771089487668/9765625)*(1-b)^13*(b-1/2)^3 + (3506461040917616/9765625)*(1-b)^14*(b-1/2)^2 + (116069532539796/1953125)*(1-b)^15*(b-1/2)^1 + (2342495287524/390625)*(1-b)^16 := by
      simp only [P5poly]; ring
    rw [hh]; positivity
  linarith

lemma stuff2f_le_S2poly {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : stuff2f b ≤ S2poly b := by
  have hu : (0:ℝ) ≤ 1-b := by linarith
  have hv : (0:ℝ) ≤ b-1/2 := by linarith
  have hb : (0:ℝ) < b := by linarith
  have hS : (0:ℝ) < (2-b)^2+b^2 := Spos h1
  have h3' : 768*b^2 ≠ 0 := by positivity
  have h4' : 163840*b^4 ≠ 0 := by positivity
  have h5' : 22020096*b^6 ≠ 0 := by positivity
  have h6' : 40960*b^2*((2-b)^2+b^2) ≠ 0 := by positivity
  have h7' : 7340032*b^4*((2-b)^2+b^2) ≠ 0 := by positivity
  have h8' : 905969664*b^6*((2-b)^2+b^2) ≠ 0 := by positivity
  have hQ' : (b^2-2*b+2) ≠ 0 := by nlinarith [sq_nonneg (b-1)]
  have hD : 123863040000000000*b^6*(b^2-2*b+2) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 6 hb.ne')) hQ'
  have hden : (0:ℝ) < 123863040000000000*b^6*(b^2-2*b+2) := by
    apply mul_pos (mul_pos (by norm_num) (pow_pos hb 6))
    nlinarith [sq_nonneg (b-1)]
  have hid : stuff2f b = ((30965760000000000)*b^8 + (-61931520000000000)*b^7
        + (62013415336567296)*b^6 + (-2257920000000000)*b^5 + (2187612000000000)*b^4
        + (46872000000000)*b^3 + (-45086062500000)*b^2 + (-1428750000000)*b + 1393818359375)
      /(123863040000000000*b^6*(b^2-2*b+2)) := by
    rw [eq_div_iff hD]
    simp only [stuff2f, K2pf, l2lo]
    field_simp
    ring
  rw [hid, div_le_iff₀ hden]
  have hcert : (0:ℝ) ≤ S2poly b * (123863040000000000*b^6*(b^2-2*b+2))
      - ((30965760000000000)*b^8 + (-61931520000000000)*b^7
        + (62013415336567296)*b^6 + (-2257920000000000)*b^5 + (2187612000000000)*b^4
        + (46872000000000)*b^3 + (-45086062500000)*b^2 + (-1428750000000)*b + 1393818359375) := by
    have hh : S2poly b * (123863040000000000*b^6*(b^2-2*b+2))
        - ((30965760000000000)*b^8 + (-61931520000000000)*b^7
        + (62013415336567296)*b^6 + (-2257920000000000)*b^5 + (2187612000000000)*b^4
        + (46872000000000)*b^3 + (-45086062500000)*b^2 + (-1428750000000)*b + 1393818359375) = 104793607922917376*(b-1/2)^13 + 1262742781959839744*(1-b)^1*(b-1/2)^12 + 4340683573863038976*(1-b)^2*(b-1/2)^11 + 11658180545096892416*(1-b)^3*(b-1/2)^10 + 26137570122661781504*(1-b)^4*(b-1/2)^9 + 40799599539136487424*(1-b)^5*(b-1/2)^8 + 41316512653626015744*(1-b)^6*(b-1/2)^7 + 27642983705491636224*(1-b)^7*(b-1/2)^6 + 13119349758979203072*(1-b)^8*(b-1/2)^5 + 4943752086971113472*(1-b)^9*(b-1/2)^4 + 1556768252227862528*(1-b)^10*(b-1/2)^3 + 358154766977581056*(1-b)^11*(b-1/2)^2 + 45903023225151488*(1-b)^12*(b-1/2)^1 + 1981810604122112*(1-b)^13 := by
      simp only [S2poly]; ring
    rw [hh]; positivity
  linarith


/-! ## Derivative assembly for the surrogate `FT` -/

lemma hasDerivAt_psi7_dl1 (b : ℝ) :
    HasDerivAt (fun b : ℝ => psi7 (dl1 b)) (dpsi7 (dl1 b) * dd1 b) b :=
  (hasDerivAt_psi7 (dl1 b)).comp b (hasDerivAt_dl1 b (Q1pos b).ne')

lemma hasDerivAt_psi7_dl2 (b : ℝ) :
    HasDerivAt (fun b : ℝ => psi7 (dl2 b)) (dpsi7 (dl2 b) * dd2 b) b :=
  (hasDerivAt_psi7 (dl2 b)).comp b (hasDerivAt_dl2 b (Q2pos b).ne')

lemma hasDerivAt_psi7_dlr (b : ℝ) :
    HasDerivAt (fun b : ℝ => psi7 (dlr b)) (dpsi7 (dlr b) * ddr b) b :=
  (hasDerivAt_psi7 (dlr b)).comp b (hasDerivAt_dlr b (Q3pos b).ne')

lemma hasDerivAt_dpsi7_dl1 (b : ℝ) :
    HasDerivAt (fun b : ℝ => dpsi7 (dl1 b) * dd1 b)
      (d2psi7 (dl1 b) * (dd1 b)^2 + dpsi7 (dl1 b) * d2d1 b) b := by
  have h1 : HasDerivAt (fun b : ℝ => dpsi7 (dl1 b)) (d2psi7 (dl1 b) * dd1 b) b :=
    (hasDerivAt_dpsi7 (dl1 b)).comp b (hasDerivAt_dl1 b (Q1pos b).ne')
  have h2 : HasDerivAt (fun b : ℝ => dd1 b) (d2d1 b) b := hasDerivAt_dd1 b (Q1pos b).ne'
  exact (h1.mul h2).congr_deriv (by ring)

lemma hasDerivAt_dpsi7_dl2 (b : ℝ) :
    HasDerivAt (fun b : ℝ => dpsi7 (dl2 b) * dd2 b)
      (d2psi7 (dl2 b) * (dd2 b)^2 + dpsi7 (dl2 b) * d2d2 b) b := by
  have h1 : HasDerivAt (fun b : ℝ => dpsi7 (dl2 b)) (d2psi7 (dl2 b) * dd2 b) b :=
    (hasDerivAt_dpsi7 (dl2 b)).comp b (hasDerivAt_dl2 b (Q2pos b).ne')
  have h2 : HasDerivAt (fun b : ℝ => dd2 b) (d2d2 b) b := hasDerivAt_dd2 b (Q2pos b).ne'
  exact (h1.mul h2).congr_deriv (by ring)

lemma hasDerivAt_dpsi7_dlr (b : ℝ) :
    HasDerivAt (fun b : ℝ => dpsi7 (dlr b) * ddr b)
      (d2psi7 (dlr b) * (ddr b)^2 + dpsi7 (dlr b) * d2dr b) b := by
  have h1 : HasDerivAt (fun b : ℝ => dpsi7 (dlr b)) (d2psi7 (dlr b) * ddr b) b :=
    (hasDerivAt_dpsi7 (dlr b)).comp b (hasDerivAt_dlr b (Q3pos b).ne')
  have h2 : HasDerivAt (fun b : ℝ => ddr b) (d2dr b) b := hasDerivAt_ddr b (Q3pos b).ne'
  exact (h1.mul h2).congr_deriv (by ring)

lemma hasDerivAt_Ctot_psi7 (b : ℝ) (hb : (0:ℝ) < 2-b) :
    HasDerivAt (fun b : ℝ => Ctot b * psi7 (dlr b))
      (dCtot b * psi7 (dlr b) + Ctot b * (dpsi7 (dlr b) * ddr b)) b :=
  ((hasDerivAt_Ctot b hb).mul (hasDerivAt_psi7_dlr b)).congr_deriv (by ring)

lemma hasDerivAt_Ctot_psi7' (b : ℝ) (hb : (0:ℝ) < 2-b) :
    HasDerivAt (fun b : ℝ => dCtot b * psi7 (dlr b) + Ctot b * (dpsi7 (dlr b) * ddr b))
      (d2Ctot b * psi7 (dlr b) + 2*(dCtot b * (dpsi7 (dlr b) * ddr b))
        + Ctot b * (d2psi7 (dlr b) * (ddr b)^2 + dpsi7 (dlr b) * d2dr b)) b := by
  have h1 : HasDerivAt (fun b : ℝ => dCtot b) (d2Ctot b) b := hasDerivAt_dCtot b hb
  have h2 : HasDerivAt (fun b : ℝ => Ctot b) (dCtot b) b := hasDerivAt_Ctot b hb
  have h3 : HasDerivAt (fun b : ℝ => psi7 (dlr b)) (dpsi7 (dlr b) * ddr b) b := hasDerivAt_psi7_dlr b
  have h4 : HasDerivAt (fun b : ℝ => dpsi7 (dlr b) * ddr b)
      (d2psi7 (dlr b) * (ddr b)^2 + dpsi7 (dlr b) * d2dr b) b := hasDerivAt_dpsi7_dlr b
  exact (h1.mul h3).add (h2.mul h4) |>.congr_deriv (by ring)

-- polynomial derivatives
noncomputable def P4poly1 (b : ℝ) : ℝ :=
  5*(2747987647/10000000000)*b^4 + 4*(-420012867/500000000)*b^3 + 3*(10380950477/10000000000)*b^2
    + 2*(-3341629571/5000000000)*b + (2080254109/10000000000)
noncomputable def P4poly2 (b : ℝ) : ℝ :=
  20*(2747987647/10000000000)*b^3 + 12*(-420012867/500000000)*b^2 + 6*(10380950477/10000000000)*b
    + 2*(-3341629571/5000000000)
noncomputable def P5poly1 (b : ℝ) : ℝ :=
  4*(841143/250000000)*b^3 + 3*(185746069/5000000000)*b^2 + 2*(-404667069/5000000000)*b
    + (396431701/10000000000)
noncomputable def P5poly2 (b : ℝ) : ℝ :=
  12*(841143/250000000)*b^2 + 6*(185746069/5000000000)*b + 2*(-404667069/5000000000)
noncomputable def S2poly1 (b : ℝ) : ℝ :=
  5*(-92469561/250000000)*b^4 + 4*(8147922281/5000000000)*b^3 + 3*(-29269999109/10000000000)*b^2
    + 2*(27261043753/10000000000)*b + (-13573620303/10000000000)
noncomputable def S2poly2 (b : ℝ) : ℝ :=
  20*(-92469561/250000000)*b^3 + 12*(8147922281/5000000000)*b^2 + 6*(-29269999109/10000000000)*b
    + 2*(27261043753/10000000000)

lemma hasDerivAt_P4poly (b : ℝ) : HasDerivAt P4poly (P4poly1 b) b := by
  have h := hasDerivAt_quint (-126736761/10000000000) (2080254109/10000000000) (-3341629571/5000000000)
    (10380950477/10000000000) (-420012867/500000000) (2747987647/10000000000) b
  rw [show P4poly = fun b : ℝ => (2747987647/10000000000)*b^5 + (-420012867/500000000)*b^4
    + (10380950477/10000000000)*b^3 + (-3341629571/5000000000)*b^2
    + (2080254109/10000000000)*b + (-126736761/10000000000) from by
      funext b; simp only [P4poly] <;> ring]
  exact h.congr_deriv (by simp only [P4poly1] <;> ring)

lemma hasDerivAt_P4poly1 (b : ℝ) : HasDerivAt P4poly1 (P4poly2 b) b := by
  have h := hasDerivAt_quart (2080254109/10000000000) (2*(-3341629571/5000000000))
    (3*(10380950477/10000000000)) (4*(-420012867/500000000)) (5*(2747987647/10000000000)) b
  rw [show P4poly1 = fun b : ℝ => (5*(2747987647/10000000000))*b^4 + (4*(-420012867/500000000))*b^3
    + (3*(10380950477/10000000000))*b^2 + (2*(-3341629571/5000000000))*b + (2080254109/10000000000)
    from by funext b; simp only [P4poly1] <;> ring]
  exact h.congr_deriv (by simp only [P4poly2] <;> ring)

lemma hasDerivAt_P5poly (b : ℝ) : HasDerivAt P5poly (P5poly1 b) b := by
  have h := hasDerivAt_quart (6764577/10000000000) (396431701/10000000000) (-404667069/5000000000)
    (185746069/5000000000) (841143/250000000) b
  rw [show P5poly = fun b : ℝ => (841143/250000000)*b^4 + (185746069/5000000000)*b^3
    + (-404667069/5000000000)*b^2 + (396431701/10000000000)*b + (6764577/10000000000) from by
      funext b; simp only [P5poly] <;> ring]
  exact h.congr_deriv (by simp only [P5poly1] <;> ring)

lemma hasDerivAt_P5poly1 (b : ℝ) : HasDerivAt P5poly1 (P5poly2 b) b := by
  have h := hasDerivAt_cubic (396431701/10000000000) (2*(-404667069/5000000000))
    (3*(185746069/5000000000)) (4*(841143/250000000)) b
  rw [show P5poly1 = fun b : ℝ => (4*(841143/250000000))*b^3 + (3*(185746069/5000000000))*b^2
    + (2*(-404667069/5000000000))*b + (396431701/10000000000) from by
      funext b; simp only [P5poly1] <;> ring]
  exact h.congr_deriv (by simp only [P5poly2] <;> ring)

lemma hasDerivAt_S2poly (b : ℝ) : HasDerivAt S2poly (S2poly1 b) b := by
  have h := hasDerivAt_quint (5359007/9765625) (-13573620303/10000000000) (27261043753/10000000000)
    (-29269999109/10000000000) (8147922281/5000000000) (-92469561/250000000) b
  rw [show S2poly = fun b : ℝ => (-92469561/250000000)*b^5 + (8147922281/5000000000)*b^4
    + (-29269999109/10000000000)*b^3 + (27261043753/10000000000)*b^2
    + (-13573620303/10000000000)*b + (5359007/9765625) from by
      funext b; simp only [S2poly] <;> ring]
  exact h.congr_deriv (by simp only [S2poly1] <;> ring)

lemma hasDerivAt_S2poly1 (b : ℝ) : HasDerivAt S2poly1 (S2poly2 b) b := by
  have h := hasDerivAt_quart (-13573620303/10000000000) (2*(27261043753/10000000000))
    (3*(-29269999109/10000000000)) (4*(8147922281/5000000000)) (5*(-92469561/250000000)) b
  rw [show S2poly1 = fun b : ℝ => (5*(-92469561/250000000))*b^4 + (4*(8147922281/5000000000))*b^3
    + (3*(-29269999109/10000000000))*b^2 + (2*(27261043753/10000000000))*b + (-13573620303/10000000000)
    from by funext b; simp only [S2poly1] <;> ring]
  exact h.congr_deriv (by simp only [S2poly2] <;> ring)

lemma hasDerivAt_LAf_I0f (b : ℝ) (hb : (0:ℝ) < 2-b) :
    HasDerivAt (fun b : ℝ => LAf b * I0f b) (dLAf b * I0f b + LAf b * dI0f b) b :=
  ((hasDerivAt_LAf b).mul (hasDerivAt_I0f b hb)).congr_deriv (by ring)

lemma hasDerivAt_LAf_I0f' (b : ℝ) (hb : (0:ℝ) < 2-b) :
    HasDerivAt (fun b : ℝ => dLAf b * I0f b + LAf b * dI0f b)
      (d2LAf b * I0f b + 2*(dLAf b * dI0f b) + LAf b * d2I0f b) b := by
  have h1 : HasDerivAt (fun b : ℝ => dLAf b) (d2LAf b) b := hasDerivAt_dLAf b
  have h2 : HasDerivAt (fun b : ℝ => LAf b) (dLAf b) b := hasDerivAt_LAf b
  have h3 : HasDerivAt (fun b : ℝ => I0f b) (dI0f b) b := hasDerivAt_I0f b hb
  have h4 : HasDerivAt (fun b : ℝ => dI0f b) (d2I0f b) b := hasDerivAt_dI0f b hb
  exact ((h1.mul h3).add (h2.mul h4)).congr_deriv (by ring)

lemma hasDerivAt_LBf_J0f (b : ℝ) (hS : (0:ℝ) < (2-b)^2+b^2) :
    HasDerivAt (fun b : ℝ => LBf b * J0f b) (dLBf b * J0f b + LBf b * dJ0f b) b :=
  ((hasDerivAt_LBf b).mul (hasDerivAt_J0f b hS)).congr_deriv (by ring)

lemma hasDerivAt_LBf_J0f' (b : ℝ) (hS : (0:ℝ) < (2-b)^2+b^2) :
    HasDerivAt (fun b : ℝ => dLBf b * J0f b + LBf b * dJ0f b)
      (d2LBf b * J0f b + 2*(dLBf b * dJ0f b) + LBf b * d2J0f b) b := by
  have h1 : HasDerivAt (fun b : ℝ => dLBf b) (d2LBf b) b := hasDerivAt_dLBf b
  have h2 : HasDerivAt (fun b : ℝ => LBf b) (dLBf b) b := hasDerivAt_LBf b
  have h3 : HasDerivAt (fun b : ℝ => J0f b) (dJ0f b) b := hasDerivAt_J0f b hS
  have h4 : HasDerivAt (fun b : ℝ => dJ0f b) (d2J0f b) b := hasDerivAt_dJ0f b hS
  exact ((h1.mul h3).add (h2.mul h4)).congr_deriv (by ring)


/-! ## The surrogate function and its derivatives -/

noncomputable def FT (b : ℝ) : ℝ :=
  (13/5)*(psi7 (dl1 b) + psi7 (dl2 b)) + Ctot b * psi7 (dlr b) + P4poly b + P5poly b
    - LAf b * I0f b - stuff1f b - LBf b * J0f b - S2poly b

noncomputable def FT1 (b : ℝ) : ℝ :=
  (13/5)*((dpsi7 (dl1 b) * dd1 b) + (dpsi7 (dl2 b) * dd2 b))
    + (dCtot b * psi7 (dlr b) + Ctot b * (dpsi7 (dlr b) * ddr b))
    + P4poly1 b + P5poly1 b
    - (dLAf b * I0f b + LAf b * dI0f b) - dStuff1f b
    - (dLBf b * J0f b + LBf b * dJ0f b) - S2poly1 b

noncomputable def FT2 (b : ℝ) : ℝ :=
  (13/5)*((d2psi7 (dl1 b) * (dd1 b)^2 + dpsi7 (dl1 b) * d2d1 b)
        + (d2psi7 (dl2 b) * (dd2 b)^2 + dpsi7 (dl2 b) * d2d2 b))
    + (d2Ctot b * psi7 (dlr b) + 2*(dCtot b * (dpsi7 (dlr b) * ddr b))
        + Ctot b * (d2psi7 (dlr b) * (ddr b)^2 + dpsi7 (dlr b) * d2dr b))
    + P4poly2 b + P5poly2 b
    - (d2LAf b * I0f b + 2*(dLAf b * dI0f b) + LAf b * d2I0f b) - d2Stuff1f b
    - (d2LBf b * J0f b + 2*(dLBf b * dJ0f b) + LBf b * d2J0f b) - S2poly2 b

lemma hasDerivAt_FT (b : ℝ) (hb : (0:ℝ) < 2-b) (hS : (0:ℝ) < (2-b)^2+b^2) :
    HasDerivAt FT (FT1 b) b := by
  have h12 : HasDerivAt (fun b : ℝ => psi7 (dl1 b) + psi7 (dl2 b))
      ((dpsi7 (dl1 b) * dd1 b) + (dpsi7 (dl2 b) * dd2 b)) b :=
    (hasDerivAt_psi7_dl1 b).add (hasDerivAt_psi7_dl2 b)
  have h1 : HasDerivAt (fun b : ℝ => (13/5)*(psi7 (dl1 b) + psi7 (dl2 b)))
      ((13/5)*((dpsi7 (dl1 b) * dd1 b) + (dpsi7 (dl2 b) * dd2 b))) b :=
    h12.const_mul (13/5)
  have h3 : HasDerivAt (fun b : ℝ => Ctot b * psi7 (dlr b))
      (dCtot b * psi7 (dlr b) + Ctot b * (dpsi7 (dlr b) * ddr b)) b := hasDerivAt_Ctot_psi7 b hb
  have h4 : HasDerivAt (fun b : ℝ => P4poly b) (P4poly1 b) b := hasDerivAt_P4poly b
  have h5 : HasDerivAt (fun b : ℝ => P5poly b) (P5poly1 b) b := hasDerivAt_P5poly b
  have h6 : HasDerivAt (fun b : ℝ => LAf b * I0f b) (dLAf b * I0f b + LAf b * dI0f b) b :=
    hasDerivAt_LAf_I0f b hb
  have h7 : HasDerivAt (fun b : ℝ => stuff1f b) (dStuff1f b) b := hasDerivAt_stuff1f b hb
  have h8 : HasDerivAt (fun b : ℝ => LBf b * J0f b) (dLBf b * J0f b + LBf b * dJ0f b) b :=
    hasDerivAt_LBf_J0f b hS
  have h9 : HasDerivAt (fun b : ℝ => S2poly b) (S2poly1 b) b := hasDerivAt_S2poly b
  have h := ((((((h1.add h3).add h4).add h5).sub h6).sub h7).sub h8).sub h9
  have hgoal : HasDerivAt (fun b : ℝ => (13/5)*(psi7 (dl1 b) + psi7 (dl2 b)) + Ctot b * psi7 (dlr b)
      + P4poly b + P5poly b - LAf b * I0f b - stuff1f b - LBf b * J0f b - S2poly b)
      ((13/5)*((dpsi7 (dl1 b) * dd1 b) + (dpsi7 (dl2 b) * dd2 b))
        + (dCtot b * psi7 (dlr b) + Ctot b * (dpsi7 (dlr b) * ddr b))
        + P4poly1 b + P5poly1 b
        - (dLAf b * I0f b + LAf b * dI0f b) - dStuff1f b
        - (dLBf b * J0f b + LBf b * dJ0f b) - S2poly1 b) b := h
  rw [show FT = fun b : ℝ => (13/5)*(psi7 (dl1 b) + psi7 (dl2 b)) + Ctot b * psi7 (dlr b)
      + P4poly b + P5poly b - LAf b * I0f b - stuff1f b - LBf b * J0f b - S2poly b from by
        funext b; simp only [FT] <;> ring]
  exact hgoal.congr_deriv (by simp only [FT1] <;> ring)

lemma hasDerivAt_FT1 (b : ℝ) (hb : (0:ℝ) < 2-b) (hS : (0:ℝ) < (2-b)^2+b^2) :
    HasDerivAt FT1 (FT2 b) b := by
  have h12 : HasDerivAt
      (fun b : ℝ => (dpsi7 (dl1 b) * dd1 b) + (dpsi7 (dl2 b) * dd2 b))
      ((d2psi7 (dl1 b) * (dd1 b)^2 + dpsi7 (dl1 b) * d2d1 b)
        + (d2psi7 (dl2 b) * (dd2 b)^2 + dpsi7 (dl2 b) * d2d2 b)) b :=
    (hasDerivAt_dpsi7_dl1 b).add (hasDerivAt_dpsi7_dl2 b)
  have h1 : HasDerivAt (fun b : ℝ => (13/5)*((dpsi7 (dl1 b) * dd1 b) + (dpsi7 (dl2 b) * dd2 b)))
      ((13/5)*((d2psi7 (dl1 b) * (dd1 b)^2 + dpsi7 (dl1 b) * d2d1 b)
        + (d2psi7 (dl2 b) * (dd2 b)^2 + dpsi7 (dl2 b) * d2d2 b))) b :=
    h12.const_mul (13/5)
  have h3 : HasDerivAt (fun b : ℝ => dCtot b * psi7 (dlr b) + Ctot b * (dpsi7 (dlr b) * ddr b))
      (d2Ctot b * psi7 (dlr b) + 2*(dCtot b * (dpsi7 (dlr b) * ddr b))
        + Ctot b * (d2psi7 (dlr b) * (ddr b)^2 + dpsi7 (dlr b) * d2dr b)) b :=
    hasDerivAt_Ctot_psi7' b hb
  have h4 : HasDerivAt (fun b : ℝ => P4poly1 b) (P4poly2 b) b := hasDerivAt_P4poly1 b
  have h5 : HasDerivAt (fun b : ℝ => P5poly1 b) (P5poly2 b) b := hasDerivAt_P5poly1 b
  have h6 : HasDerivAt (fun b : ℝ => dLAf b * I0f b + LAf b * dI0f b)
      (d2LAf b * I0f b + 2*(dLAf b * dI0f b) + LAf b * d2I0f b) b := hasDerivAt_LAf_I0f' b hb
  have h7 : HasDerivAt (fun b : ℝ => dStuff1f b) (d2Stuff1f b) b := hasDerivAt_dStuff1f b hb
  have h8 : HasDerivAt (fun b : ℝ => dLBf b * J0f b + LBf b * dJ0f b)
      (d2LBf b * J0f b + 2*(dLBf b * dJ0f b) + LBf b * d2J0f b) b := hasDerivAt_LBf_J0f' b hS
  have h9 : HasDerivAt (fun b : ℝ => S2poly1 b) (S2poly2 b) b := hasDerivAt_S2poly1 b
  have h := ((((((h1.add h3).add h4).add h5).sub h6).sub h7).sub h8).sub h9
  have hgoal : HasDerivAt (fun b : ℝ => (13/5)*((dpsi7 (dl1 b) * dd1 b) + (dpsi7 (dl2 b) * dd2 b))
      + (dCtot b * psi7 (dlr b) + Ctot b * (dpsi7 (dlr b) * ddr b))
      + P4poly1 b + P5poly1 b
      - (dLAf b * I0f b + LAf b * dI0f b) - dStuff1f b
      - (dLBf b * J0f b + LBf b * dJ0f b) - S2poly1 b)
      ((13/5)*((d2psi7 (dl1 b) * (dd1 b)^2 + dpsi7 (dl1 b) * d2d1 b)
        + (d2psi7 (dl2 b) * (dd2 b)^2 + dpsi7 (dl2 b) * d2d2 b))
      + (d2Ctot b * psi7 (dlr b) + 2*(dCtot b * (dpsi7 (dlr b) * ddr b))
        + Ctot b * (d2psi7 (dlr b) * (ddr b)^2 + dpsi7 (dlr b) * d2dr b))
      + P4poly2 b + P5poly2 b
      - (d2LAf b * I0f b + 2*(dLAf b * dI0f b) + LAf b * d2I0f b) - d2Stuff1f b
      - (d2LBf b * J0f b + 2*(dLBf b * dJ0f b) + LBf b * d2J0f b) - S2poly2 b) b := h
  rw [show FT1 = fun b : ℝ => (13/5)*((dpsi7 (dl1 b) * dd1 b) + (dpsi7 (dl2 b) * dd2 b))
      + (dCtot b * psi7 (dlr b) + Ctot b * (dpsi7 (dlr b) * ddr b))
      + P4poly1 b + P5poly1 b
      - (dLAf b * I0f b + LAf b * dI0f b) - dStuff1f b
      - (dLBf b * J0f b + LBf b * dJ0f b) - S2poly1 b from by
        funext b; simp only [FT1] <;> ring]
  exact hgoal.congr_deriv (by simp only [FT2] <;> ring)


/-! ## Bounds on the second derivative of `FT` -/

lemma abs_mul_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a*b| ≤ A*B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) (le_trans (abs_nonneg _) ha)

lemma mul_le_of_abs_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : a*b ≤ A*B :=
  le_trans (le_abs_self _) (abs_mul_le ha hb)

lemma neg_mul_le_of_abs_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : -(A*B) ≤ a*b :=
  le_trans (abs_le.mp (abs_mul_le ha hb)).1 (le_refl _)

lemma abs_sq_le_sq {x A : ℝ} (h : |x| ≤ A) : |x^2| ≤ A^2 := by
  rw [abs_of_nonneg (sq_nonneg x)]
  rw [← sq_abs x]
  exact pow_le_pow_left₀ (abs_nonneg x) h 2

lemma sq_le_of_abs_le {x A : ℝ} (h : |x| ≤ A) : x^2 ≤ A^2 := by
  rw [← sq_abs x]
  exact pow_le_pow_left₀ (abs_nonneg x) h 2

lemma abs_psi7_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : |psi7 x| ≤ 1 := by
  obtain ⟨h1, h2⟩ := psi7_range hx0 hx1
  rw [abs_of_nonneg h1]; exact h2

lemma dd1_nonneg {b : ℝ} (h2 : b ≤ 1) : 0 ≤ dd1 b := by
  rw [dd1]
  apply div_nonneg _ (by positivity)
  nlinarith [sq_nonneg (b - 3/2), h2]

lemma P4poly2_le {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : P4poly2 b ≤ 8 := by
  rw [P4poly2]
  nlinarith [h1, h2, sq_nonneg b, pow_nonneg (by linarith : (0:ℝ) ≤ b) 3]

lemma P5poly2_le {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : P5poly2 b ≤ 1/4 := by
  rw [P5poly2]
  nlinarith [h1, h2, sq_nonneg b]

lemma S2poly2_nonneg {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : 0 ≤ S2poly2 b := by
  rw [S2poly2]
  nlinarith [h1, h2, sq_nonneg b, sq_nonneg (b - 1), sq_nonneg (b - 1/2)]

lemma d2Ctot_nonpos {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : d2Ctot b ≤ 0 := by
  have hpos : (0:ℝ) < 2-b := by linarith
  rw [d2Ctot_nice b hpos]
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith [sq_nonneg (1-b), pow_nonneg (by linarith : (0:ℝ) ≤ 1-b) 3,
      pow_nonneg (by linarith : (0:ℝ) ≤ 1-b) 4]
  · positivity

lemma FT2_le {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : FT2 b ≤ 20 := by
  have hb1 : (0:ℝ) < b := by linarith
  have hb2 : (0:ℝ) < 2-b := by linarith
  have hS : (0:ℝ) < (2-b)^2+b^2 := Spos h1
  obtain ⟨hdl1a, hdl1b⟩ := dl1_range h1 h2
  obtain ⟨hdl2a, hdl2b⟩ := dl2_range h1 h2
  obtain ⟨hdlra, hdlrb⟩ := dlr_range h1 h2
  -- ingredient bounds
  have hA2 : |d2psi7 (dl1 b)| ≤ 2 := abs_d2psi7_le_two hdl1a (by linarith)
  have hA1 : |dpsi7 (dl1 b)| ≤ 1 := abs_dpsi7_le_one hdl1a (by linarith)
  have hB2 : |d2psi7 (dl2 b)| ≤ 2 := abs_d2psi7_le_two hdl2a (by linarith)
  have hB1 : |dpsi7 (dl2 b)| ≤ 1 := abs_dpsi7_le_one hdl2a (by linarith)
  have hR2 : |d2psi7 (dlr b)| ≤ 2 := abs_d2psi7_le_two hdlra (by linarith)
  have hR1 : |dpsi7 (dlr b)| ≤ 1 := abs_dpsi7_le_one hdlra (by linarith)
  have hR0 : |psi7 (dlr b)| ≤ 1 := abs_psi7_le_one hdlra (by linarith)
  have hdd1 : |dd1 b| ≤ 1/2 := abs_le.mpr ⟨by linarith [dd1_nonneg h2], dd1_le h1 h2⟩
  have hd2d1 : |d2d1 b| ≤ 3/5 := abs_le.mpr ⟨by linarith [d2d1_ge h1 h2], by linarith [d2d1_le h1 h2]⟩
  have hdd2 : |dd2 b| ≤ 1/8 := abs_le.mpr ⟨by linarith [dd2_ge h1 h2], by linarith [dd2_le h1 h2]⟩
  have hd2d2 : |d2d2 b| ≤ 1/4 := abs_le.mpr ⟨by linarith [d2d2_ge h1 h2], by linarith [d2d2_le h1 h2]⟩
  have hddr : |ddr b| ≤ 1/2 := abs_le.mpr ⟨by linarith [ddr_ge h1 h2], ddr_le h1 h2⟩
  have hd2dr : |d2dr b| ≤ 1/4 := abs_le.mpr ⟨by linarith [d2dr_ge h1 h2], d2dr_le h1 h2⟩
  obtain ⟨hCt0, hCt2⟩ := Ctot_bounds h1 h2
  have hdCt : dCtot b ≤ 0 := dCtot_nonpos h2
  have hd2Ct : d2Ctot b ≤ 0 := d2Ctot_nonpos h1 h2
  obtain ⟨hLA0, hLA2⟩ := LAf_bounds2 (by linarith) h2
  have hdLA0 : dLAf b ≤ 0 := (LAf_bounds (by linarith) h2).2.1
  have hdLA1 : -1 ≤ dLAf b := dLAf_ge (by linarith) h2
  have hd2LA0 : d2LAf b ≤ 0 := d2LAf_nonpos (by linarith)
  have hd2LA1 : -1 ≤ d2LAf b := (LAf_bounds (by linarith) h2).2.2
  obtain ⟨hLB0, hLB2⟩ := LBf_bounds2 h1 h2
  obtain ⟨hLB3, hLB4, hLB5, hLB6, hLB7⟩ := LBf_bounds h1 h2
  obtain ⟨hI0a, hI0b⟩ := I0f_bounds2 h1 h2
  obtain ⟨hJ0a, hJ0b⟩ := J0f_bounds2 h1 h2
  have hdI0 : |dI0f b| ≤ 7/384 := abs_le.mpr ⟨by linarith [dI0f_ge h1 h2], by linarith [dI0f_le h1 h2]⟩
  have hd2I0 : |d2I0f b| ≤ 7/128 := abs_le.mpr ⟨by linarith [d2I0f_ge h1 h2], by linarith [d2I0f_le h1 h2]⟩
  have hdJ0 : |dJ0f b| ≤ 7/768 := abs_le.mpr ⟨by linarith [dJ0f_ge h1 h2], by linarith [dJ0f_le h1 h2]⟩
  have hd2J0 : |d2J0f b| ≤ 7/384 := abs_le.mpr ⟨by linarith [d2J0f_ge h1 h2], by linarith [d2J0f_le h1 h2]⟩
  obtain ⟨hd2S1a, hd2S1b⟩ := d2Stuff1f_bounds h1 h2
  -- bounds on the individual summands
  have t1 : d2psi7 (dl1 b) * (dd1 b)^2 + dpsi7 (dl1 b) * d2d1 b ≤ 11/10 := by
    have h1' : d2psi7 (dl1 b) * (dd1 b)^2 ≤ 2*((1/2)^2) := mul_le_of_abs_le hA2 (abs_sq_le_sq hdd1)
    have h2' : dpsi7 (dl1 b) * d2d1 b ≤ 1*(3/5) := mul_le_of_abs_le hA1 hd2d1
    linarith
  have t2 : d2psi7 (dl2 b) * (dd2 b)^2 + dpsi7 (dl2 b) * d2d2 b ≤ 3/4 := by
    have h1' : d2psi7 (dl2 b) * (dd2 b)^2 ≤ 2*((1/8)^2) := mul_le_of_abs_le hB2 (abs_sq_le_sq hdd2)
    have h2' : dpsi7 (dl2 b) * d2d2 b ≤ 1*(1/4) := mul_le_of_abs_le hB1 hd2d2
    linarith
  have t3 : d2Ctot b * psi7 (dlr b) + 2*(dCtot b * (dpsi7 (dlr b) * ddr b))
      + Ctot b * (d2psi7 (dlr b) * (ddr b)^2 + dpsi7 (dlr b) * d2dr b) ≤ 3/2 := by
    have hR0pos : 0 ≤ psi7 (dlr b) := (psi7_range hdlra (by linarith)).1
    have hR1pos : 0 ≤ dpsi7 (dlr b) := dpsi7_nonneg hdlra (by linarith)
    have hddrpos : 0 ≤ ddr b := ddr_ge h1 h2
    have h1' : d2Ctot b * psi7 (dlr b) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hd2Ct hR0pos
    have h2' : dCtot b * (dpsi7 (dlr b) * ddr b) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hdCt (mul_nonneg hR1pos hddrpos)
    have h3a : d2psi7 (dlr b) * (ddr b)^2 ≤ 2*((1/2)^2) := mul_le_of_abs_le hR2 (abs_sq_le_sq hddr)
    have h3b : dpsi7 (dlr b) * d2dr b ≤ 1*(1/4) := mul_le_of_abs_le hR1 hd2dr
    have h3c : d2psi7 (dlr b) * (ddr b)^2 + dpsi7 (dlr b) * d2dr b ≤ 3/4 := by linarith
    have h3d : Ctot b * (d2psi7 (dlr b) * (ddr b)^2 + dpsi7 (dlr b) * d2dr b) ≤ 2*(3/4) := by
      by_cases hp : 0 ≤ d2psi7 (dlr b) * (ddr b)^2 + dpsi7 (dlr b) * d2dr b
      · exact mul_le_mul hCt2 h3c hp (by norm_num)
      · have hn : d2psi7 (dlr b) * (ddr b)^2 + dpsi7 (dlr b) * d2dr b ≤ 0 := by linarith
        have : Ctot b * (d2psi7 (dlr b) * (ddr b)^2 + dpsi7 (dlr b) * d2dr b) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hCt0 hn
        linarith
    linarith
  have t6 : d2LAf b * I0f b + 2*(dLAf b * dI0f b) + LAf b * d2I0f b ≥ -2/5 := by
    have h2' : 0 ≤ 2*(dLAf b * dI0f b) := by
      have : 0 ≤ dLAf b * dI0f b := mul_nonneg_of_nonpos_of_nonpos hdLA0 (dI0f_le h1 h2)
      linarith
    have h3' : (-7/128)*2 ≤ LAf b * d2I0f b := by
      have habs : |LAf b * d2I0f b| ≤ 2*(7/128) := abs_mul_le
        (abs_le.mpr ⟨by linarith [hLA0], hLA2⟩) hd2I0
      linarith [(abs_le.mp habs).1]
    by_cases hp : 0 ≤ d2LAf b
    · have : 0 ≤ d2LAf b * I0f b := mul_nonneg hp hI0a
      linarith
    · have hn : d2LAf b ≤ 0 := by linarith
      have : d2LAf b * I0f b ≥ d2LAf b * (1/4) := mul_le_mul_of_nonpos_left hI0b hn
      nlinarith [hd2LA1]
  have t7 : d2LBf b * J0f b + 2*(dLBf b * dJ0f b) + LBf b * d2J0f b ≥ -11/10 := by
    have h2' : 2*((2)*(-7/768)) ≤ 2*(dLBf b * dJ0f b) := by
      have h1' : dLBf b * (-7/768) ≤ dLBf b * dJ0f b :=
        mul_le_mul_of_nonneg_left (dJ0f_ge h1 h2) hLB4
      have h2'' : 2 * (-7/768) ≤ dLBf b * (-7/768) := by nlinarith [hLB5]
      linarith
    have h3' : -(2*(7/384)) ≤ LBf b * d2J0f b := by
      have habs : |LBf b * d2J0f b| ≤ 2*(7/384) := abs_mul_le
        (abs_le.mpr ⟨by linarith [hLB0], hLB2⟩) hd2J0
      linarith [(abs_le.mp habs).1]
    by_cases hp : 0 ≤ d2LBf b
    · have : 0 ≤ d2LBf b * J0f b := mul_nonneg hp hJ0a
      linarith
    · have hn : d2LBf b ≤ 0 := by linarith
      have hge : -4 ≤ d2LBf b := hLB7
      have hJ : J0f b ≤ 1/4 := hJ0b
      have : d2LBf b * J0f b ≥ (-4)*(1/4) := by
        nlinarith [hge, hJ, hn, hJ0a]
      linarith
  rw [FT2]
  linarith [t1, t2, t3, t6, t7, P4poly2_le h1 h2, P5poly2_le h1 h2, S2poly2_nonneg h1 h2,
    d2Stuff1f_bounds h1 h2]


/-! ## The chord lower bound and the region III assembly -/

theorem chord_lower {f f' f'' : ℝ → ℝ} {c d M : ℝ} (hcd : c < d)
    (hf : ∀ x ∈ Set.Icc c d, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc c d, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x ∈ Set.Icc c d, f'' x ≤ M) :
    ∀ β ∈ Set.Icc c d,
      ((d - β) * f c + (β - c) * f d) / (d - c) - M * (β - c) * (d - β) / 2 ≤ f β := by
  have hq : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (M / 2) * ((x - c) * (d - x)))
      ((M / 2) * (c + d - 2 * x)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => (x - c) * (d - x)) ((d - x) - (x - c)) x := by
      have ha : HasDerivAt (fun x : ℝ => x - c) 1 x := by
        simpa using (hasDerivAt_id x).sub_const c
      have hb : HasDerivAt (fun x : ℝ => d - x) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub d
      have h := ha.mul hb
      refine h.congr_deriv ?_
      ring
    have h := h1.const_mul (M / 2)
    refine h.congr_deriv ?_
    ring
  have hq' : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (M / 2) * (c + d - 2 * x)) (-M) x := by
    intro x
    have ha : HasDerivAt (fun x : ℝ => c + d - 2 * x) (-2) x := by
      have hc : HasDerivAt (fun x : ℝ => 2 * x) 2 x := by
        simpa using (hasDerivAt_id x).const_mul (2:ℝ)
      have h := (hasDerivAt_const (x := x) (c := c + d)).sub hc
      refine h.congr_deriv ?_
      ring
    have h := ha.const_mul (M / 2)
    refine h.congr_deriv ?_
    ring
  have hphi : ∀ x ∈ Set.Icc c d, HasDerivAt (fun x : ℝ => f x + (M / 2) * ((x - c) * (d - x)))
      (f' x + (M / 2) * (c + d - 2 * x)) x := fun x hx => (hf x hx).add (hq x)
  have hphi' : ∀ x ∈ Set.Icc c d, HasDerivAt (fun x : ℝ => f' x + (M / 2) * (c + d - 2 * x))
      (f'' x - M) x := fun x hx => (hf' x hx).add (hq' x)
  have hcf : ContinuousOn f (Set.Icc c d) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (fun x : ℝ => f x + (M / 2) * ((x - c) * (d - x))) (Set.Icc c d) := by
    exact hcf.add (by fun_prop)
  have hconc : ConcaveOn ℝ (Set.Icc c d) (fun x : ℝ => f x + (M / 2) * ((x - c) * (d - x))) := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc c d) hcont
    · intro x hx; exact (hphi x (interior_subset hx)).hasDerivWithinAt
    · intro x hx; exact (hphi' x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      have := hf'' x (interior_subset hx)
      linarith
  intro β hβ
  have hdc : 0 < d - c := by linarith
  have ha : (0:ℝ) ≤ (d - β) / (d - c) := div_nonneg (by linarith [hβ.2]) hdc.le
  have hb : (0:ℝ) ≤ (β - c) / (d - c) := div_nonneg (by linarith [hβ.1]) hdc.le
  have hab : (d - β) / (d - c) + (β - c) / (d - c) = 1 := by
    field_simp; ring
  have harg : ((d - β) / (d - c)) • c + ((β - c) / (d - c)) • d = β := by
    rw [smul_eq_mul, smul_eq_mul]
    field_simp
    ring
  have hc0 : f c + M / 2 * ((c - c) * (d - c)) = f c := by ring
  have hd0 : f d + M / 2 * ((d - c) * (d - d)) = f d := by ring
  have hdef := hconc.2 (Set.left_mem_Icc.mpr hcd.le) (Set.right_mem_Icc.mpr hcd.le) ha hb hab
  rw [harg] at hdef
  rw [smul_eq_mul, smul_eq_mul] at hdef
  simp only [] at hdef
  rw [hc0, hd0] at hdef
  have hcomb : ((d - β) / (d - c)) * f c + ((β - c) / (d - c)) * f d
      = ((d - β) * f c + (β - c) * f d) / (d - c) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
  rw [hcomb] at hdef
  have h : M / 2 * ((β - c) * (d - β)) = M * (β - c) * (d - β) / 2 := by ring
  linarith [hdef, h]


lemma chord_block {c d M : ℝ} (hcd : c < d) (hM : 0 ≤ M)
    (hf : ∀ x ∈ Set.Icc c d, HasDerivAt FT (FT1 x) x)
    (hf' : ∀ x ∈ Set.Icc c d, HasDerivAt FT1 (FT2 x) x)
    (hf'' : ∀ x ∈ Set.Icc c d, FT2 x ≤ M)
    (hc0 : (3:ℝ)/10 + M*(d-c)^2/8 ≤ FT c) (hd0 : (3:ℝ)/10 + M*(d-c)^2/8 ≤ FT d) :
    ∀ β ∈ Set.Icc c d, (3:ℝ)/10 ≤ FT β := by
  intro β hβ
  have h := chord_lower hcd hf hf' hf'' β hβ
  have hquad : M*(β-c)*(d-β)/2 ≤ M*(d-c)^2/8 := by
    have hq : (β-c)*(d-β) ≤ (d-c)^2/4 := by nlinarith [sq_nonneg (2*β-c-d)]
    nlinarith [hq, hM]
  have h1 : 0 ≤ (d-β)/(d-c) := div_nonneg (by linarith [hβ.2]) (by linarith)
  have h2 : 0 ≤ (β-c)/(d-c) := div_nonneg (by linarith [hβ.1]) (by linarith)
  have h3 : (d-β)/(d-c) + (β-c)/(d-c) = 1 := by
    have hdc : (d-c) ≠ 0 := by linarith
    have hsum2 : (d-β) + (β-c) = d-c := by ring
    rw [← add_div, hsum2, div_self hdc]
  have hkey : (3:ℝ)/10 + M*(d-c)^2/8 ≤ ((d-β)/(d-c))*FT c + ((β-c)/(d-c))*FT d := by
    have ha := mul_le_mul_of_nonneg_left hc0 h1
    have hb := mul_le_mul_of_nonneg_left hd0 h2
    have hsum : ((d-β)/(d-c))*((3:ℝ)/10 + M*(d-c)^2/8) + ((β-c)/(d-c))*((3:ℝ)/10 + M*(d-c)^2/8)
        = (3:ℝ)/10 + M*(d-c)^2/8 := by rw [← add_mul, h3, one_mul]
    calc (3:ℝ)/10 + M*(d-c)^2/8
        = ((d-β)/(d-c))*((3:ℝ)/10 + M*(d-c)^2/8) + ((β-c)/(d-c))*((3:ℝ)/10 + M*(d-c)^2/8) := hsum.symm
      _ ≤ ((d-β)/(d-c))*FT c + ((β-c)/(d-c))*FT d := add_le_add ha hb
  have hcomb : ((d-β)*FT c + (β-c)*FT d)/(d-c) = ((d-β)/(d-c))*FT c + ((β-c)/(d-c))*FT d := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
  rw [hcomb] at h
  linarith

lemma FT_node (i : ℕ) (hi : i ≤ 32) :
    (3:ℝ)/10 + 5/8192 ≤ FT ((1:ℝ)/2 + i/64) := by
  interval_cases i <;>
    norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf,
      S2poly, l2lo, l2hi]

lemma FT_node_0 : (12313/40960 : ℝ) ≤ FT (1/2 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_1 : (12313/40960 : ℝ) ≤ FT (33/64 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_2 : (12313/40960 : ℝ) ≤ FT (17/32 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_3 : (12313/40960 : ℝ) ≤ FT (35/64 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_4 : (12313/40960 : ℝ) ≤ FT (9/16 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_5 : (12313/40960 : ℝ) ≤ FT (37/64 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_6 : (12313/40960 : ℝ) ≤ FT (19/32 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_7 : (12313/40960 : ℝ) ≤ FT (39/64 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_8 : (12313/40960 : ℝ) ≤ FT (5/8 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_9 : (12313/40960 : ℝ) ≤ FT (41/64 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_10 : (12313/40960 : ℝ) ≤ FT (21/32 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_11 : (12313/40960 : ℝ) ≤ FT (43/64 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_12 : (12313/40960 : ℝ) ≤ FT (11/16 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_13 : (12313/40960 : ℝ) ≤ FT (45/64 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_14 : (12313/40960 : ℝ) ≤ FT (23/32 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_15 : (12313/40960 : ℝ) ≤ FT (47/64 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_16 : (12313/40960 : ℝ) ≤ FT (3/4 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_17 : (12313/40960 : ℝ) ≤ FT (49/64 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_18 : (12313/40960 : ℝ) ≤ FT (25/32 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_19 : (12313/40960 : ℝ) ≤ FT (51/64 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_20 : (12313/40960 : ℝ) ≤ FT (13/16 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_21 : (12313/40960 : ℝ) ≤ FT (53/64 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_22 : (12313/40960 : ℝ) ≤ FT (27/32 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_23 : (12313/40960 : ℝ) ≤ FT (55/64 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_24 : (12313/40960 : ℝ) ≤ FT (7/8 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_25 : (12313/40960 : ℝ) ≤ FT (57/64 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_26 : (12313/40960 : ℝ) ≤ FT (29/32 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_27 : (12313/40960 : ℝ) ≤ FT (59/64 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_28 : (12313/40960 : ℝ) ≤ FT (15/16 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_29 : (12313/40960 : ℝ) ≤ FT (61/64 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_30 : (12313/40960 : ℝ) ≤ FT (31/32 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_31 : (12313/40960 : ℝ) ≤ FT (63/64 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]
lemma FT_node_32 : (12313/40960 : ℝ) ≤ FT (1/1 : ℝ) := by
  norm_num [FT, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, LBf, I0f, J0f, stuff1f, K1pf, S2poly, l2lo, l2hi]

theorem FT_ge {b : ℝ} (h1 : (1:ℝ)/2 ≤ b) (h2 : b ≤ 1) : (3:ℝ)/10 ≤ FT b := by
  have hD1 : ∀ x ∈ Set.Icc (1/2:ℝ) 1, HasDerivAt FT (FT1 x) x :=
    fun x hx => hasDerivAt_FT x (by linarith [hx.2]) (Spos hx.1)
  have hD2 : ∀ x ∈ Set.Icc (1/2:ℝ) 1, HasDerivAt FT1 (FT2 x) x :=
    fun x hx => hasDerivAt_FT1 x (by linarith [hx.2]) (Spos hx.1)
  have hD3 : ∀ x ∈ Set.Icc (1/2:ℝ) 1, FT2 x ≤ 20 := fun x hx => FT2_le hx.1 hx.2
  by_cases hb1 : b ≤ (33/64 : ℝ)
  · refine chord_block (c := (1/2 : ℝ)) (d := (33/64 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨h1, hb1⟩
    · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · linarith [FT_node_0]
    · linarith [FT_node_1]
  ·
    by_cases hb2 : b ≤ (17/32 : ℝ)
    · refine chord_block (c := (33/64 : ℝ)) (d := (17/32 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb1], hb2⟩
      · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
      · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
      · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
      · linarith [FT_node_1]
      · linarith [FT_node_2]
    ·
      by_cases hb3 : b ≤ (35/64 : ℝ)
      · refine chord_block (c := (17/32 : ℝ)) (d := (35/64 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb2], hb3⟩
        · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
        · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
        · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
        · linarith [FT_node_2]
        · linarith [FT_node_3]
      ·
        by_cases hb4 : b ≤ (9/16 : ℝ)
        · refine chord_block (c := (35/64 : ℝ)) (d := (9/16 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb3], hb4⟩
          · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
          · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
          · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
          · linarith [FT_node_3]
          · linarith [FT_node_4]
        ·
          by_cases hb5 : b ≤ (37/64 : ℝ)
          · refine chord_block (c := (9/16 : ℝ)) (d := (37/64 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb4], hb5⟩
            · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
            · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
            · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
            · linarith [FT_node_4]
            · linarith [FT_node_5]
          ·
            by_cases hb6 : b ≤ (19/32 : ℝ)
            · refine chord_block (c := (37/64 : ℝ)) (d := (19/32 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb5], hb6⟩
              · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
              · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
              · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
              · linarith [FT_node_5]
              · linarith [FT_node_6]
            ·
              by_cases hb7 : b ≤ (39/64 : ℝ)
              · refine chord_block (c := (19/32 : ℝ)) (d := (39/64 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb6], hb7⟩
                · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                · linarith [FT_node_6]
                · linarith [FT_node_7]
              ·
                by_cases hb8 : b ≤ (5/8 : ℝ)
                · refine chord_block (c := (39/64 : ℝ)) (d := (5/8 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb7], hb8⟩
                  · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                  · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                  · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                  · linarith [FT_node_7]
                  · linarith [FT_node_8]
                ·
                  by_cases hb9 : b ≤ (41/64 : ℝ)
                  · refine chord_block (c := (5/8 : ℝ)) (d := (41/64 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb8], hb9⟩
                    · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                    · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                    · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                    · linarith [FT_node_8]
                    · linarith [FT_node_9]
                  ·
                    by_cases hb10 : b ≤ (21/32 : ℝ)
                    · refine chord_block (c := (41/64 : ℝ)) (d := (21/32 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb9], hb10⟩
                      · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                      · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                      · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                      · linarith [FT_node_9]
                      · linarith [FT_node_10]
                    ·
                      by_cases hb11 : b ≤ (43/64 : ℝ)
                      · refine chord_block (c := (21/32 : ℝ)) (d := (43/64 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb10], hb11⟩
                        · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                        · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                        · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                        · linarith [FT_node_10]
                        · linarith [FT_node_11]
                      ·
                        by_cases hb12 : b ≤ (11/16 : ℝ)
                        · refine chord_block (c := (43/64 : ℝ)) (d := (11/16 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb11], hb12⟩
                          · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                          · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                          · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                          · linarith [FT_node_11]
                          · linarith [FT_node_12]
                        ·
                          by_cases hb13 : b ≤ (45/64 : ℝ)
                          · refine chord_block (c := (11/16 : ℝ)) (d := (45/64 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb12], hb13⟩
                            · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                            · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                            · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                            · linarith [FT_node_12]
                            · linarith [FT_node_13]
                          ·
                            by_cases hb14 : b ≤ (23/32 : ℝ)
                            · refine chord_block (c := (45/64 : ℝ)) (d := (23/32 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb13], hb14⟩
                              · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                              · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                              · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                              · linarith [FT_node_13]
                              · linarith [FT_node_14]
                            ·
                              by_cases hb15 : b ≤ (47/64 : ℝ)
                              · refine chord_block (c := (23/32 : ℝ)) (d := (47/64 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb14], hb15⟩
                                · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                · linarith [FT_node_14]
                                · linarith [FT_node_15]
                              ·
                                by_cases hb16 : b ≤ (3/4 : ℝ)
                                · refine chord_block (c := (47/64 : ℝ)) (d := (3/4 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb15], hb16⟩
                                  · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                  · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                  · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                  · linarith [FT_node_15]
                                  · linarith [FT_node_16]
                                ·
                                  by_cases hb17 : b ≤ (49/64 : ℝ)
                                  · refine chord_block (c := (3/4 : ℝ)) (d := (49/64 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb16], hb17⟩
                                    · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                    · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                    · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                    · linarith [FT_node_16]
                                    · linarith [FT_node_17]
                                  ·
                                    by_cases hb18 : b ≤ (25/32 : ℝ)
                                    · refine chord_block (c := (49/64 : ℝ)) (d := (25/32 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb17], hb18⟩
                                      · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                      · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                      · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                      · linarith [FT_node_17]
                                      · linarith [FT_node_18]
                                    ·
                                      by_cases hb19 : b ≤ (51/64 : ℝ)
                                      · refine chord_block (c := (25/32 : ℝ)) (d := (51/64 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb18], hb19⟩
                                        · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                        · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                        · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                        · linarith [FT_node_18]
                                        · linarith [FT_node_19]
                                      ·
                                        by_cases hb20 : b ≤ (13/16 : ℝ)
                                        · refine chord_block (c := (51/64 : ℝ)) (d := (13/16 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb19], hb20⟩
                                          · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                          · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                          · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                          · linarith [FT_node_19]
                                          · linarith [FT_node_20]
                                        ·
                                          by_cases hb21 : b ≤ (53/64 : ℝ)
                                          · refine chord_block (c := (13/16 : ℝ)) (d := (53/64 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb20], hb21⟩
                                            · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                            · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                            · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                            · linarith [FT_node_20]
                                            · linarith [FT_node_21]
                                          ·
                                            by_cases hb22 : b ≤ (27/32 : ℝ)
                                            · refine chord_block (c := (53/64 : ℝ)) (d := (27/32 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb21], hb22⟩
                                              · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                              · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                              · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                              · linarith [FT_node_21]
                                              · linarith [FT_node_22]
                                            ·
                                              by_cases hb23 : b ≤ (55/64 : ℝ)
                                              · refine chord_block (c := (27/32 : ℝ)) (d := (55/64 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb22], hb23⟩
                                                · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                · linarith [FT_node_22]
                                                · linarith [FT_node_23]
                                              ·
                                                by_cases hb24 : b ≤ (7/8 : ℝ)
                                                · refine chord_block (c := (55/64 : ℝ)) (d := (7/8 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb23], hb24⟩
                                                  · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                  · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                  · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                  · linarith [FT_node_23]
                                                  · linarith [FT_node_24]
                                                ·
                                                  by_cases hb25 : b ≤ (57/64 : ℝ)
                                                  · refine chord_block (c := (7/8 : ℝ)) (d := (57/64 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb24], hb25⟩
                                                    · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                    · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                    · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                    · linarith [FT_node_24]
                                                    · linarith [FT_node_25]
                                                  ·
                                                    by_cases hb26 : b ≤ (29/32 : ℝ)
                                                    · refine chord_block (c := (57/64 : ℝ)) (d := (29/32 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb25], hb26⟩
                                                      · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                      · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                      · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                      · linarith [FT_node_25]
                                                      · linarith [FT_node_26]
                                                    ·
                                                      by_cases hb27 : b ≤ (59/64 : ℝ)
                                                      · refine chord_block (c := (29/32 : ℝ)) (d := (59/64 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb26], hb27⟩
                                                        · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                        · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                        · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                        · linarith [FT_node_26]
                                                        · linarith [FT_node_27]
                                                      ·
                                                        by_cases hb28 : b ≤ (15/16 : ℝ)
                                                        · refine chord_block (c := (59/64 : ℝ)) (d := (15/16 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb27], hb28⟩
                                                          · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                          · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                          · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                          · linarith [FT_node_27]
                                                          · linarith [FT_node_28]
                                                        ·
                                                          by_cases hb29 : b ≤ (61/64 : ℝ)
                                                          · refine chord_block (c := (15/16 : ℝ)) (d := (61/64 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb28], hb29⟩
                                                            · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                            · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                            · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                            · linarith [FT_node_28]
                                                            · linarith [FT_node_29]
                                                          ·
                                                            by_cases hb30 : b ≤ (31/32 : ℝ)
                                                            · refine chord_block (c := (61/64 : ℝ)) (d := (31/32 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb29], hb30⟩
                                                              · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                              · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                              · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                              · linarith [FT_node_29]
                                                              · linarith [FT_node_30]
                                                            ·
                                                              by_cases hb31 : b ≤ (63/64 : ℝ)
                                                              · refine chord_block (c := (31/32 : ℝ)) (d := (63/64 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb30], hb31⟩
                                                                · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                                · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                                · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                                · linarith [FT_node_30]
                                                                · linarith [FT_node_31]
                                                              ·
                                                                · refine chord_block (c := (63/64 : ℝ)) (d := (1 : ℝ)) (M := 20) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ b ⟨by linarith [hb31], h2⟩
                                                                  · exact fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                                  · exact fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                                  · exact fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
                                                                  · linarith [FT_node_31]
                                                                  · linarith [FT_node_32]



open Set

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## A. The second majorant: branch integrand and its integrals -/

/-- The `else`-branch integrand of the second majorant. -/
noncomputable def Eterm (β s : ℝ) : ℝ := (2-β)*β/(s*Real.sqrt ((2-β)^2+s^2))

/-- The `log`-branch integrand of the second majorant. -/
noncomputable def Lterm (β s : ℝ) : ℝ :=
  Real.log ((4*β^2+s^2)/(2*β*s))*(1 - s^2/(2*((2-β)^2+β^2)))

lemma hasDerivAt_Eterm_anti {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/2) :
    ∀ s ∈ Set.uIcc (1/4:ℝ) (1/2),
      HasDerivAt (fun s : ℝ => -β*Real.arsinh ((2-β)/s)) (Eterm β s) s := by
  intro s hs
  rw [Set.uIcc_of_le (by norm_num : (1:ℝ)/4 ≤ 1/2)] at hs
  have hs0 : 0 < s := by linarith [hs.1]
  have hA : (0:ℝ) < 2-β := by linarith
  have h1 : HasDerivAt (fun s : ℝ => (2-β)/s) (-(2-β)/s^2) s := by
    have h := (hasDerivAt_const (x := s) (c := 2-β)).div (hasDerivAt_id s) (ne_of_gt hs0)
    have hfun : ((fun _ : ℝ => (2-β)) / id) = fun t : ℝ => (2-β)/t := by
      funext t; simp only [Pi.div_apply, id_eq]
    rw [hfun] at h
    exact h.congr_deriv (by simp only [id_eq]; ring)
  have h2 : HasDerivAt (fun y : ℝ => Real.arsinh y) (Real.sqrt (1 + ((2-β)/s)^2))⁻¹ ((2-β)/s) :=
    Real.hasDerivAt_arsinh ((2-β)/s)
  have h3 : HasDerivAt (fun s : ℝ => Real.arsinh ((2-β)/s))
      ((Real.sqrt (1 + ((2-β)/s)^2))⁻¹ * (-(2-β)/s^2)) s := h2.comp s h1
  have h4 : HasDerivAt (fun s : ℝ => -β*Real.arsinh ((2-β)/s))
      (-β * ((Real.sqrt (1 + ((2-β)/s)^2))⁻¹ * (-(2-β)/s^2))) s := h3.const_mul (-β)
  refine h4.congr_deriv ?_
  simp only [Eterm]
  have hsq : Real.sqrt (1 + ((2-β)/s)^2) = Real.sqrt ((2-β)^2+s^2)/s := by
    have h1' : 1 + ((2-β)/s)^2 = ((2-β)^2+s^2)/s^2 := by field_simp; ring
    rw [h1', Real.sqrt_div (by positivity : (0:ℝ) ≤ (2-β)^2+s^2),
      show Real.sqrt ((s:ℝ)^2) = s from Real.sqrt_sq (le_of_lt hs0)]
  rw [hsq]
  have hsp : Real.sqrt ((2-β)^2+s^2) ≠ 0 := by positivity
  field_simp <;> ring

lemma integral_E_Icc {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/2) :
    (∫ s in (1/4:ℝ)..(1/2), Eterm β s) = β*(Real.arsinh (4*(2-β)) - Real.arsinh (2*(2-β))) := by
  have hcont : ContinuousOn (fun s : ℝ => Eterm β s) (Set.uIcc (1/4:ℝ) (1/2)) := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ)/4 ≤ 1/2)] at hs
    have hs0 : 0 < s := by linarith [hs.1]
    apply ContinuousAt.continuousWithinAt
    simp only [Eterm]
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (hasDerivAt_Eterm_anti hβ0 hβ1)
    (hcont.intervalIntegrable)]
  rw [show ((2-β)/((1:ℝ)/2)) = 2*(2-β) by ring]
  rw [show ((2-β)/((1:ℝ)/4)) = 4*(2-β) by ring]
  ring

lemma integral_E_half {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1/2) (hβ4 : (1:ℝ)/4 ≤ β) :
    (∫ s in β..(1/2), Eterm β s)
      = β*(Real.arsinh ((2-β)/β) - Real.arsinh (2*(2-β))) := by
  have hcont : ContinuousOn (fun s : ℝ => Eterm β s) (Set.uIcc β (1/2)) := by
    intro s hs
    rw [Set.uIcc_of_le hβ1] at hs
    have hs0 : 0 < s := by linarith [hs.1, hβ0]
    apply ContinuousAt.continuousWithinAt
    simp only [Eterm]
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)
  have hderiv : ∀ s ∈ Set.uIcc β (1/2),
      HasDerivAt (fun s : ℝ => -β*Real.arsinh ((2-β)/s)) (Eterm β s) s := by
    intro s hs
    apply hasDerivAt_Eterm_anti hβ0 hβ1
    rw [Set.uIcc_of_le hβ1] at hs
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ)/4 ≤ 1/2)]
    exact ⟨by linarith [hs.1], hs.2⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  rw [show ((2-β)/((1:ℝ)/2)) = 2*(2-β) by ring]
  ring

/-! ## B. Series bounds for `log (4b)` -/

/-- The eighth-order Taylor upper bound of `log (4b)` around `b = 1/4`. -/
noncomputable def logUb (b : ℝ) : ℝ :=
  l2hi - ∑ k ∈ Finset.range 8, (1-2*b)^(k+1)/((k:ℝ)+1)

noncomputable def dlogUb (b : ℝ) : ℝ := ∑ k ∈ Finset.range 8, 2*(1-2*b)^k

noncomputable def d2logUb (b : ℝ) : ℝ := -∑ k ∈ Finset.range 7, 4*((k:ℝ)+1)*(1-2*b)^k

/-- Lower Taylor bound of `log (4b)`. -/
noncomputable def logLb (b : ℝ) : ℝ :=
  l2lo - (∑ k ∈ Finset.range 8, (1-2*b)^(k+1)/((k:ℝ)+1)) - 2*(1-2*b)^9/9

noncomputable def dlogLb (b : ℝ) : ℝ :=
  (∑ k ∈ Finset.range 8, 2*(1-2*b)^k) + 4*(1-2*b)^8

noncomputable def d2logLb (b : ℝ) : ℝ :=
  -(∑ k ∈ Finset.range 7, 4*((k:ℝ)+1)*(1-2*b)^k) - 64*(1-2*b)^7


lemma hasDerivAt_c1m2b (b : ℝ) : HasDerivAt (fun t : ℝ => 1 - 2*t) (-2) b := by
  have hfun : (fun t : ℝ => 1 - 2*t) = (fun t : ℝ => (-2)*t + 1) := by funext t; ring
  rw [hfun]
  exact (hasDerivAt_lin (1:ℝ) (-2) b).congr_deriv (by ring)

lemma hasDerivAt_sum_log (b : ℝ) :
    HasDerivAt (fun t : ℝ => ∑ k ∈ Finset.range 8, (1-2*t)^(k+1)/((k:ℝ)+1))
      (∑ k ∈ Finset.range 8, -(2*(1-2*b)^k)) b := by
  have h2 := hasDerivAt_c1m2b b
  refine HasDerivAt.fun_sum ?_
  intro k hk
  have hk1 : HasDerivAt (fun t : ℝ => (1-2*t)^(k+1)) (((k+1:ℕ):ℝ) * (1-2*b)^k * (-2)) b := by
    have h := h2.pow (k+1)
    refine h.congr_deriv ?_
    norm_num
  have hk2 := hk1.div_const (((k:ℝ)+1))
  refine hk2.congr_deriv ?_
  have hne : ((k:ℝ)+1) ≠ 0 := by positivity
  rw [show ((k+1:ℕ):ℝ) = ((k:ℝ)+1) by push_cast; ring]
  field_simp

lemma hasDerivAt_sum_exp (b : ℝ) :
    HasDerivAt (fun t : ℝ => ∑ k ∈ Finset.range 8, 2*(1-2*t)^k)
      (∑ k ∈ Finset.range 8, -(4*(k:ℝ)*(1-2*b)^(k-1))) b := by
  have h2 := hasDerivAt_c1m2b b
  refine HasDerivAt.fun_sum ?_
  intro k hk
  have hk1 : HasDerivAt (fun t : ℝ => (1-2*t)^k) ((k:ℝ) * (1-2*b)^(k-1) * (-2)) b :=
    h2.pow k
  refine (hk1.const_mul (2:ℝ)).congr_deriv ?_
  ring

lemma hasDerivAt_logUb (b : ℝ) : HasDerivAt logUb (dlogUb b) b := by
  have hsum := hasDerivAt_sum_log b
  have hconst : HasDerivAt (fun _ : ℝ => l2hi) 0 b := hasDerivAt_const b l2hi
  have hfun : logUb = fun t : ℝ => l2hi - ∑ k ∈ Finset.range 8, (1-2*t)^(k+1)/((k:ℝ)+1) := rfl
  rw [hfun]
  refine (hconst.sub hsum).congr_deriv ?_
  simp only [dlogUb, Finset.sum_neg_distrib, zero_sub, neg_neg]

lemma hasDerivAt_dlogUb (b : ℝ) : HasDerivAt dlogUb (d2logUb b) b := by
  have hsum := hasDerivAt_sum_exp b
  have hfun : dlogUb = fun t : ℝ => ∑ k ∈ Finset.range 8, 2*(1-2*t)^k := rfl
  rw [hfun]
  refine hsum.congr_deriv ?_
  simp only [d2logUb, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

lemma hasDerivAt_logLb (b : ℝ) : HasDerivAt logLb (dlogLb b) b := by
  have h2 := hasDerivAt_c1m2b b
  have hsum := hasDerivAt_sum_log b
  have h9 : HasDerivAt (fun t : ℝ => (1-2*t)^9) (9 * (1-2*b)^8 * (-2)) b := by
    have h := h2.pow 9
    refine h.congr_deriv ?_
    norm_num
  have h9' : HasDerivAt (fun t : ℝ => 2*(1-2*t)^9/9) (-4*(1-2*b)^8) b := by
    have h := h9.const_mul (2/9)
    have hfun : (fun y : ℝ => 2/9 * (1-2*y)^9) = fun t : ℝ => 2*(1-2*t)^9/9 := by
      funext t; ring
    rw [hfun] at h
    refine h.congr_deriv ?_
    ring
  have hconst : HasDerivAt (fun _ : ℝ => l2lo) 0 b := hasDerivAt_const b l2lo
  have hfun : logLb = fun t : ℝ =>
      l2lo - (∑ k ∈ Finset.range 8, (1-2*t)^(k+1)/((k:ℝ)+1)) - 2*(1-2*t)^9/9 := rfl
  rw [hfun]
  refine ((hconst.sub hsum).sub h9').congr_deriv ?_
  simp only [dlogLb, Finset.sum_neg_distrib, zero_sub, neg_neg]
  ring

lemma hasDerivAt_dlogLb (b : ℝ) : HasDerivAt dlogLb (d2logLb b) b := by
  have h2 := hasDerivAt_c1m2b b
  have hsum := hasDerivAt_sum_exp b
  have h8 : HasDerivAt (fun t : ℝ => 4*(1-2*t)^8) (-64*(1-2*b)^7) b := by
    have h := h2.pow 8
    have hh := h.const_mul (4:ℝ)
    refine hh.congr_deriv ?_
    norm_num
    ring
  have hfun : dlogLb = fun t : ℝ => (∑ k ∈ Finset.range 8, 2*(1-2*t)^k) + 4*(1-2*t)^8 := rfl
  rw [hfun]
  refine (hsum.add h8).congr_deriv ?_
  simp only [d2logLb, Finset.sum_range_succ, Finset.sum_range_zero]
  ring


/-! ## C. The `Lb` and `Eb` surrogates and their derivatives -/


/-! ## C. Region-II surrogates `Lb`, `Eb` and their derivatives -/

macro "hcl" : tactic => `(tactic|
  first
    | rfl
    | (funext t; simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.neg_apply,
        Pi.pow_apply, Pi.inv_apply, id_eq, div_eq_mul_inv, mul_inv]; ring_nf)
    | (funext t; simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.neg_apply,
        Pi.pow_apply, Pi.inv_apply, id_eq, div_eq_mul_inv, mul_inv]; done)
    | (simp only [id_eq, one_mul, mul_one, mul_zero, add_zero, div_eq_mul_inv, mul_inv]; ring_nf)
    | (simp only [id_eq, one_mul, mul_one, mul_zero, add_zero, div_eq_mul_inv, mul_inv]; done)
    | (funext t; ring_nf)
    | ring_nf
    | (field_simp; ring_nf)
    | (field_simp; done)
    | done)

lemma hasDerivAt_idf (b : ℝ) : HasDerivAt (fun t : ℝ => t) 1 b := by
  convert (hasDerivAt_id b) using 1 <;> hcl

noncomputable def rhof (b : ℝ) : ℝ := (16*b^2-1)/(64*b^2+1)

noncomputable def drhof (b : ℝ) : ℝ := 160*b/(64*b^2+1)^2

lemma hasDerivAt_rhof (b : ℝ) : HasDerivAt rhof (drhof b) b := by
  have hnum : HasDerivAt (fun t : ℝ => 16*t^2-1) (32*b) b := by
    have h := hasDerivAt_quad (-1:ℝ) 0 16 b
    have hfun : (fun t : ℝ => 16*t^2 + 0*t + (-1)) = fun t : ℝ => 16*t^2-1 := by
      funext t; ring
    rw [hfun] at h
    convert h using 1 <;> hcl
  have hden : HasDerivAt (fun t : ℝ => 64*t^2+1) (128*b) b := by
    have h := hasDerivAt_quad (1:ℝ) 0 64 b
    have hfun : (fun t : ℝ => 64*t^2 + 0*t + 1) = fun t : ℝ => 64*t^2+1 := by
      funext t; ring
    rw [hfun] at h
    convert h using 1 <;> hcl
  have hdiv := hnum.div hden (by positivity)
  have hfun : ((fun t : ℝ => 16*t^2-1) / (fun t : ℝ => 64*t^2+1)) = rhof := by
    funext t; simp only [rhof, Pi.div_apply]
  have hkey : (32*b*(64*b^2+1) - (16*b^2-1)*(128*b))/(64*b^2+1)^2 = drhof b := by
    simp only [drhof]; ring_nf
  rw [hfun, hkey] at hdiv
  convert hdiv using 1 <;> hcl

/-- `2b² - 4b + 4 = (2-b)² + b²`. -/
noncomputable def Sb (b : ℝ) : ℝ := 2*b^2 - 4*b + 4

lemma hasDerivAt_Sb (b : ℝ) : HasDerivAt Sb (4*b-4) b := by
  have h := hasDerivAt_quad (4:ℝ) (-4) 2 b
  have hfun : (fun t : ℝ => 2*t^2 + (-4)*t + 4) = Sb := by funext t; simp only [Sb]; ring
  rw [hfun] at h
  convert h using 1 <;> hcl

lemma Sb_pos (b : ℝ) : (0:ℝ) < Sb b := by
  simp only [Sb]; nlinarith [sq_nonneg (b-1)]

lemma hasDerivAt_sq (b : ℝ) : HasDerivAt (fun t : ℝ => t^2) (2*b) b := by
  have h := hasDerivAt_quad (0:ℝ) 0 1 b
  convert h using 1 <;> (first | rfl | (funext t; ring) | ring | done)

lemma hasDerivAt_cube (b : ℝ) : HasDerivAt (fun t : ℝ => t^3) (3*b^2) b := by
  have h := hasDerivAt_cubic (0:ℝ) 0 0 1 b
  convert h using 1 <;> (first | rfl | (funext t; ring) | ring | done)

/-! ### The first piece `P1f` -/

noncomputable def P1f (b : ℝ) : ℝ := l2hi*((b-1/4) - (b^3-1/64)/(6*Sb b))

noncomputable def P1f1 (b : ℝ) : ℝ :=
  l2hi*(1 - (3*b^2*Sb b - (b^3-1/64)*(4*b-4))/(6*(Sb b)^2))

noncomputable def P1f2 (b : ℝ) : ℝ :=
  -(108304247/7500000000)*(128*b^3 - 771*b^2 + 774*b - 2)/(Sb b)^3

lemma hasDerivAt_P1f (b : ℝ) : HasDerivAt P1f (P1f1 b) b := by
  have h1 : HasDerivAt (fun t : ℝ => t - 1/4) 1 b :=
    (hasDerivAt_idf b).sub_const (1/4)
  have h2 : HasDerivAt (fun t : ℝ => t^3 - 1/64) (3*b^2) b :=
    (hasDerivAt_cube b).sub_const (1/64)
  have hSb : HasDerivAt (fun t : ℝ => 6*Sb t) (6*(4*b-4)) b := (hasDerivAt_Sb b).const_mul 6
  have h4 : HasDerivAt (fun t : ℝ => (t^3-1/64)/(6*Sb t))
      ((3*b^2 * (6*Sb b) - (b^3-1/64) * (6*(4*b-4)))/(6*Sb b)^2) b :=
    h2.div hSb (by have := Sb_pos b; positivity)
  have h5 : HasDerivAt (fun t : ℝ => l2hi*((t-1/4) - (t^3-1/64)/(6*Sb t)))
      (l2hi*(1 - ((3*b^2 * (6*Sb b) - (b^3-1/64) * (6*(4*b-4)))/(6*Sb b)^2))) b :=
    (h1.sub h4).const_mul l2hi
  convert h5 using 1 <;> (first | rfl | (simp only [P1f1, l2hi, Sb]; field_simp; try ring) | (simp only [P1f1, l2hi, Sb]; ring_nf) | ring | done)

lemma hasDerivAt_P1f1 (b : ℝ) : HasDerivAt P1f1 (P1f2 b) b := by
  have hA : HasDerivAt (fun t : ℝ => (3*t^2)*Sb t) ((3*(2*b))*Sb b + (3*b^2)*(4*b-4)) b :=
    (hasDerivAt_sq b).const_mul 3 |>.mul (hasDerivAt_Sb b)
  have hB : HasDerivAt (fun t : ℝ => (t^3-1/64)*(4*t-4))
      ((3*b^2)*(4*b-4) + (b^3-1/64)*4) b := by
    have h2' : HasDerivAt (fun t : ℝ => t^3 - 1/64) (3*b^2) b :=
      (hasDerivAt_cube b).sub_const (1/64)
    have h3' : HasDerivAt (fun t : ℝ => 4*t-4) 4 b := by
      have h := ((hasDerivAt_idf b).sub_const 1).const_mul 4
      convert h using 1 <;> hcl
    exact h2'.mul h3'
  have hN : HasDerivAt (fun t : ℝ => (3*t^2)*Sb t - (t^3-1/64)*(4*t-4))
      (((3*(2*b))*Sb b + (3*b^2)*(4*b-4)) - ((3*b^2)*(4*b-4) + (b^3-1/64)*4)) b :=
    hA.sub hB
  have hD : HasDerivAt (fun t : ℝ => 6*(Sb t)^2) (6*(2*(Sb b)*(4*b-4))) b := by
    have h0 : HasDerivAt (fun t : ℝ => (Sb t)^2) (2*(Sb b)*(4*b-4)) b := by
      have h := (hasDerivAt_Sb b).pow 2
      convert h using 1 <;> (first | rfl | (funext t; simp only [Pi.pow_apply]) | (push_cast; ring_nf) | ring | done)
    exact h0.const_mul 6
  have hdiv := hN.div hD (by have h0 := Sb_pos b; positivity)
  have hone : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 b := hasDerivAt_const b 1
  have hfin := (hone.sub hdiv).const_mul l2hi
  convert hfin using 1 <;> (first | rfl | (simp only [P1f1, P1f2, l2hi, Sb]; field_simp; try ring) | (simp only [P1f1, P1f2, l2hi, Sb]; ring_nf) | ring | done)

/-! ### The second piece `P2f` -/

noncomputable def P2f (b : ℝ) : ℝ := (b*logUb b - 7*b/8 + 1/4 - 1/(128*b))/2

noncomputable def P2f1 (b : ℝ) : ℝ := (logUb b + b*dlogUb b - 7/8 + 1/(128*b^2))/2

noncomputable def P2f2 (b : ℝ) : ℝ := dlogUb b + b/2*d2logUb b - 1/(128*b^3)

lemma hasDerivAt_recip_mul {b : ℝ} (hb : b ≠ 0) :
    HasDerivAt (fun t : ℝ => 1/(128*t)) (-(1/(128*b^2))) b := by
  have hinv : HasDerivAt (fun t : ℝ => (t)⁻¹) (-(b^2)⁻¹) b := hasDerivAt_inv hb
  have h := (hasDerivAt_const (x := b) (c := (1:ℝ)/128)).mul hinv
  convert h using 1 <;> (first | hcl | (funext t; simp only [Pi.mul_apply, div_eq_mul_inv, mul_inv]) | (simp only [div_eq_mul_inv, mul_inv]; field_simp; try ring) | (simp only [div_eq_mul_inv, mul_inv]; ring_nf))

lemma hasDerivAt_recip_mul_sq {b : ℝ} (hb : b ≠ 0) :
    HasDerivAt (fun t : ℝ => 1/(128*t^2)) (-(1/(64*b^3))) b := by
  have hsq : HasDerivAt (fun t : ℝ => t^2) (2*b) b := hasDerivAt_sq b
  have hinv : HasDerivAt (fun t : ℝ => (t^2)⁻¹) (-(2*b)/(b^2)^2) b :=
    hsq.inv (pow_ne_zero 2 hb)
  have h := (hasDerivAt_const (x := b) (c := (1:ℝ)/128)).mul hinv
  have hkey : (0 * (b^2)⁻¹ + (1:ℝ)/128 * (-(2*b)/(b^2)^2)) = -(1/(64*b^3)) := by
    rw [zero_mul, zero_add]
    field_simp
    ring
  rw [hkey] at h
  convert h using 1 <;> (first | hcl | (funext t; simp only [Pi.mul_apply, div_eq_mul_inv, mul_inv]))

lemma hasDerivAt_P2f {b : ℝ} (hb : b ≠ 0) : HasDerivAt P2f (P2f1 b) b := by
  have h1 : HasDerivAt (fun t : ℝ => t*logUb t) (logUb b + b*dlogUb b) b := by
    have h := (hasDerivAt_idf b).mul (hasDerivAt_logUb b)
    convert h using 1 <;> hcl
  have h2 : HasDerivAt (fun t : ℝ => 7*t/8) (7/8) b := by
    have h := (hasDerivAt_idf b).const_mul (7/8)
    convert h using 1 <;> hcl
  have h3 : HasDerivAt (fun _ : ℝ => (1:ℝ)/4) 0 b := hasDerivAt_const b (1/4)
  have h6 : HasDerivAt (fun t : ℝ => t*logUb t - 7*t/8 + 1/4 - 1/(128*t))
      ((logUb b + b*dlogUb b) - 7/8 + 0 - (-(1/(128*b^2)))) b :=
    ((h1.sub h2).add h3).sub (hasDerivAt_recip_mul hb)
  have hfin := h6.const_mul (1/2)
  convert hfin using 1 <;> (first | rfl | (funext t; simp only [P2f]; ring) | (simp only [P2f1]; field_simp; try ring) | (simp only [P2f1]; ring_nf) | ring | done)

lemma hasDerivAt_P2f1 {b : ℝ} (hb : b ≠ 0) : HasDerivAt P2f1 (P2f2 b) b := by
  have h1 : HasDerivAt (fun t : ℝ => logUb t) (dlogUb b) b := hasDerivAt_logUb b
  have h2 : HasDerivAt (fun t : ℝ => t*dlogUb t) (dlogUb b + b*d2logUb b) b := by
    have h := (hasDerivAt_idf b).mul (hasDerivAt_dlogUb b)
    convert h using 1 <;> hcl
  have h3 : HasDerivAt (fun _ : ℝ => (7:ℝ)/8) 0 b := hasDerivAt_const b (7/8)
  have h6 : HasDerivAt (fun t : ℝ => logUb t + t*dlogUb t - 7/8 + 1/(128*t^2))
      (dlogUb b + (dlogUb b + b*d2logUb b) - 0 + (-(1/(64*b^3)))) b :=
    ((h1.add h2).sub h3).add (hasDerivAt_recip_mul_sq hb)
  have hfin := h6.const_mul (1/2)
  convert hfin using 1 <;> (first | rfl | (funext t; simp only [P2f1]; ring) | (simp only [P2f2]; field_simp; try ring) | (simp only [P2f2]; ring_nf) | ring | done)

/-! ### The third piece `P3f` -/

noncomputable def P3f (b : ℝ) : ℝ := ((b-1/4) - 2*b*rhof b + b*(rhof b)^2)/2

noncomputable def P3f1 (b : ℝ) : ℝ := (147456*b^6 - 768*b^4 - 192*b^2 + 4)/(2*(64*b^2+1)^3)

noncomputable def P3f2 (b : ℝ) : ℝ := 960*b*(512*b^4+24*b^2-1)/(64*b^2+1)^4

lemma hasDerivAt_P3f (b : ℝ) : HasDerivAt P3f (P3f1 b) b := by
  have h1 : HasDerivAt (fun t : ℝ => t - 1/4) 1 b :=
    (hasDerivAt_idf b).sub_const (1/4)
  have h2 : HasDerivAt (fun t : ℝ => (2*t)*rhof t) ((2*1)*rhof b + (2*b)*drhof b) b := by
    have h := ((hasDerivAt_idf b).const_mul 2).mul (hasDerivAt_rhof b)
    convert h using 1 <;> hcl
  have hsq : HasDerivAt (fun t : ℝ => (rhof t)^2) (2*rhof b*drhof b) b := by
    have h := (hasDerivAt_rhof b).pow 2
    convert h using 1 <;> (first | rfl | (funext t; simp only [Pi.pow_apply]) | (push_cast; ring_nf) | ring | done)
  have h3 : HasDerivAt (fun t : ℝ => t*(rhof t)^2) (1*(rhof b)^2 + b*(2*rhof b*drhof b)) b := by
    have h := (hasDerivAt_idf b).mul hsq
    convert h using 1 <;> hcl
  have hfin := (((h1.sub h2).add h3)).const_mul (1/2)
  convert hfin using 1 <;> (first | rfl | (funext t; simp only [P3f, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply, Pi.pow_apply]; ring) | (simp only [P3f1, rhof, drhof]; field_simp; try ring) | (simp only [P3f1, rhof, drhof]; ring_nf) | ring | done)

lemma hasDerivAt_P3f1 (b : ℝ) : HasDerivAt P3f1 (P3f2 b) b := by
  have hnum : HasDerivAt (fun t : ℝ => 147456*t^6 - 768*t^4 - 192*t^2 + 4)
      (147456*(6*b^5) - 768*(4*b^3) - 192*(2*b)) b := by
    have h := hasDerivAt_sext (4:ℝ) 0 (-192) 0 (-768) 0 147456 b
    have hfun : (fun t : ℝ => 147456*t^6 + 0*t^5 + (-768)*t^4 + 0*t^3 + (-192)*t^2 + 0*t + 4)
        = fun t : ℝ => 147456*t^6 - 768*t^4 - 192*t^2 + 4 := by funext t; ring
    rw [hfun] at h
    convert h using 1 <;> (first | rfl | (funext t; ring) | ring | done)
  have hden : HasDerivAt (fun t : ℝ => 2*(64*t^2+1)^3) (2*(3*(64*b^2+1)^2*(128*b))) b := by
    have hq : HasDerivAt (fun t : ℝ => 64*t^2+1) (128*b) b := by
      have h := hasDerivAt_quad (1:ℝ) 0 64 b
      have hfun : (fun t : ℝ => 64*t^2 + 0*t + 1) = fun t : ℝ => 64*t^2+1 := by funext t; ring
      rw [hfun] at h
      convert h using 1 <;> hcl
    have h1 : HasDerivAt (fun t : ℝ => (64*t^2+1)^3) (3*(64*b^2+1)^2*(128*b)) b := by
      have h0 := hq.pow 3
      convert h0 using 1 <;> (first | rfl | (funext t; simp only [Pi.pow_apply]) | (push_cast; ring_nf) | ring | done)
    exact h1.const_mul 2
  have h := hnum.div hden (by positivity)
  have hfun : ((fun t : ℝ => 147456*t^6 - 768*t^4 - 192*t^2 + 4) / (fun t : ℝ => 2*(64*t^2+1)^3)) = P3f1 := by
    funext t; simp only [P3f1, Pi.div_apply]
  have hkey : ((147456*(6*b^5) - 768*(4*b^3) - 192*(2*b))*(2*(64*b^2+1)^3)
        - (147456*b^6 - 768*b^4 - 192*b^2 + 4)*(2*(3*(64*b^2+1)^2*(128*b))))
      / (2*(64*b^2+1)^3)^2 = P3f2 b := by
    simp only [P3f2]; field_simp; ring
  rw [hfun, hkey] at h
  convert h using 1 <;> hcl


/-! ## D. `Lb`, `Eb`, their derivative chains and second-derivative bounds -/

noncomputable def Lb (b : ℝ) : ℝ := P1f b + P2f b + P3f b

noncomputable def Lb1 (b : ℝ) : ℝ := P1f1 b + P2f1 b + P3f1 b

noncomputable def Lb2 (b : ℝ) : ℝ := P1f2 b + P2f2 b + P3f2 b

lemma hasDerivAt_Lb {b : ℝ} (hb : b ≠ 0) : HasDerivAt Lb (Lb1 b) b := by
  have h := ((hasDerivAt_P1f b).add (hasDerivAt_P2f hb)).add (hasDerivAt_P3f b)
  convert h using 1 <;> (first | rfl | (funext t; simp only [Lb, Pi.add_apply]; ring) | (simp only [Lb1]; ring) | ring | done)

lemma hasDerivAt_Lb1 {b : ℝ} (hb : b ≠ 0) : HasDerivAt Lb1 (Lb2 b) b := by
  have h := ((hasDerivAt_P1f1 b).add (hasDerivAt_P2f1 hb)).add (hasDerivAt_P3f1 b)
  convert h using 1 <;> (first | rfl | (funext t; simp only [Lb1, Pi.add_apply]; ring) | (simp only [Lb2]; ring) | ring | done)

noncomputable def E1f (b : ℝ) : ℝ := -b*logLb b

noncomputable def E1f1 (b : ℝ) : ℝ := -logLb b - b*dlogLb b

noncomputable def E1f2 (b : ℝ) : ℝ := -2*dlogLb b - b*d2logLb b

noncomputable def E3f (b : ℝ) : ℝ := b*(4*b^2-1)/(16*(2-b)^2)

noncomputable def E3f1 (b : ℝ) : ℝ := -(4*b^3-24*b^2+b+2)/(16*(2-b)^3)

noncomputable def E3f2 (b : ℝ) : ℝ := (47*b-4)/(8*(2-b)^4)

noncomputable def E4f (b : ℝ) : ℝ := 3*b/(512*(2-b)^4)

noncomputable def E4f1 (b : ℝ) : ℝ := (9*b+6)/(512*(2-b)^5)

noncomputable def E4f2 (b : ℝ) : ℝ := 3*(3*b+4)/(128*(2-b)^6)

lemma hasDerivAt_E1f (b : ℝ) : HasDerivAt E1f (E1f1 b) b := by
  have h := (hasDerivAt_idf b).mul (hasDerivAt_logLb b) |>.neg
  convert h using 1 <;> (first | rfl | (funext t; simp only [E1f, Pi.mul_apply, Pi.neg_apply, id_eq]; ring) | (simp only [E1f1, id_eq]; ring) | ring | done)

lemma hasDerivAt_E1f1 (b : ℝ) : HasDerivAt E1f1 (E1f2 b) b := by
  have h := (hasDerivAt_logLb b).neg.sub ((hasDerivAt_idf b).mul (hasDerivAt_dlogLb b))
  convert h using 1 <;> (first | rfl | (funext t; simp only [E1f1, Pi.sub_apply, Pi.neg_apply, Pi.mul_apply, id_eq]; ring) | (simp only [E1f2]; ring) | ring | done)

lemma hasDerivAt_E3f {b : ℝ} (hbb : b ≤ 1) : HasDerivAt E3f (E3f1 b) b := by
  have h2b : (0:ℝ) < 2-b := by linarith
  have hnum : HasDerivAt (fun t : ℝ => 4*t^3 - t) (12*b^2 - 1) b := by
    have h := hasDerivAt_cubic (0:ℝ) (-1) 0 4 b
    convert h using 1 <;> (first | rfl | (funext t; ring) | ring | done)
  have hden : HasDerivAt (fun t : ℝ => 16*(2-t)^2) (16*(2*b-4)) b := by
    have h := hasDerivAt_2ms2 b
    convert (h.const_mul 16) using 1 <;> (first | rfl | (funext t; ring) | ring | done)
  have hdiv := hnum.div hden (by have := h2b; positivity)
  have hfun : ((fun t : ℝ => 4*t^3 - t) / (fun t : ℝ => 16*(2-t)^2)) = E3f := by
    funext t; simp only [E3f, Pi.div_apply]; try ring
  have hkey : ((12*b^2 - 1)*(16*(2-b)^2) - (4*b^3-b)*(16*(2*b-4)))/(16*(2-b)^2)^2 = E3f1 b := by
    simp only [E3f1]; field_simp; ring
  rw [hfun, hkey] at hdiv
  convert hdiv using 1 <;> hcl

lemma hasDerivAt_E3f1 {b : ℝ} (hbb : b ≤ 1) : HasDerivAt E3f1 (E3f2 b) b := by
  have h2b : (0:ℝ) < 2-b := by linarith
  have hnum : HasDerivAt (fun t : ℝ => -(4*t^3 - 24*t^2 + t + 2)) (-(12*b^2 - 48*b + 1)) b := by
    have h := hasDerivAt_cubic (2:ℝ) 1 (-24) 4 b
    convert (h.neg) using 1 <;> (first | rfl | (funext t; simp only [Pi.neg_apply]; ring) | ring | done)
  have hden : HasDerivAt (fun t : ℝ => 16*(2-t)^3) (16*(3*(-1)*b^2 + 2*(6)*b^1 + (-12))) b := by
    have h := hasDerivAt_2ms3 b
    convert (h.const_mul 16) using 1 <;> (first | rfl | (funext t; ring) | ring | done)
  have hdiv := hnum.div hden (by have := h2b; positivity)
  have hfun : ((fun t : ℝ => -(4*t^3 - 24*t^2 + t + 2)) / (fun t : ℝ => 16*(2-t)^3)) = E3f1 := by
    funext t; simp only [E3f1, Pi.div_apply]; try ring
  have hkey : ((-(12*b^2 - 48*b + 1))*(16*(2-b)^3) - (-(4*b^3-24*b^2+b+2))*(16*(3*(-1)*b^2 + 2*(6)*b^1 + (-12))))
      /(16*(2-b)^3)^2 = E3f2 b := by
    simp only [E3f2]; field_simp; ring
  rw [hfun, hkey] at hdiv
  convert hdiv using 1 <;> hcl

lemma hasDerivAt_E4f {b : ℝ} (hbb : b ≤ 1) : HasDerivAt E4f (E4f1 b) b := by
  have h2b : (0:ℝ) < 2-b := by linarith
  have hnum : HasDerivAt (fun t : ℝ => 3*t) 3 b := by
    have h := (hasDerivAt_idf b).const_mul 3
    convert h using 1 <;> (first | rfl | (funext t; ring) | ring | done)
  have hden : HasDerivAt (fun t : ℝ => 512*(2-t)^4) (512*(4*(1)*b^3 + 3*(-8)*b^2 + 2*(24)*b^1 + (-32))) b := by
    have h := hasDerivAt_2ms4 b
    convert (h.const_mul 512) using 1 <;> (first | rfl | (funext t; ring) | ring | done)
  have hdiv := hnum.div hden (by have := h2b; positivity)
  have hfun : ((fun t : ℝ => 3*t) / (fun t : ℝ => 512*(2-t)^4)) = E4f := by
    funext t; simp only [E4f, Pi.div_apply]; try ring
  have hkey : (3*(512*(2-b)^4) - (3*b)*(512*(4*(1)*b^3 + 3*(-8)*b^2 + 2*(24)*b^1 + (-32))))/(512*(2-b)^4)^2 = E4f1 b := by
    simp only [E4f1]; field_simp; ring
  rw [hfun, hkey] at hdiv
  convert hdiv using 1 <;> hcl

lemma hasDerivAt_E4f1 {b : ℝ} (hbb : b ≤ 1) : HasDerivAt E4f1 (E4f2 b) b := by
  have h2b : (0:ℝ) < 2-b := by linarith
  have hnum : HasDerivAt (fun t : ℝ => 9*t + 6) 9 b := by
    have h := hasDerivAt_lin (6:ℝ) 9 b
    convert h using 1 <;> (first | rfl | (funext t; ring) | ring | done)
  have hden : HasDerivAt (fun t : ℝ => 512*(2-t)^5)
      (512*(5*(-1)*b^4 + 4*(10)*b^3 + 3*(-40)*b^2 + 2*(80)*b^1 + (-80))) b := by
    have h := hasDerivAt_2ms5 b
    convert (h.const_mul 512) using 1 <;> (first | rfl | (funext t; ring) | ring | done)
  have hdiv := hnum.div hden (by have := h2b; positivity)
  have hfun : ((fun t : ℝ => 9*t + 6) / (fun t : ℝ => 512*(2-t)^5)) = E4f1 := by
    funext t; simp only [E4f1, Pi.div_apply]; try ring
  have hkey : (9*(512*(2-b)^5) - (9*b+6)*(512*(5*(-1)*b^4 + 4*(10)*b^3 + 3*(-40)*b^2 + 2*(80)*b^1 + (-80))))
      /(512*(2-b)^5)^2 = E4f2 b := by
    simp only [E4f2]; field_simp; ring
  rw [hfun, hkey] at hdiv
  convert hdiv using 1 <;> hcl

noncomputable def Eb (b : ℝ) : ℝ := E1f b + b*l2hi + E3f b + E4f b

noncomputable def Eb1 (b : ℝ) : ℝ := E1f1 b + l2hi + E3f1 b + E4f1 b

noncomputable def Eb2 (b : ℝ) : ℝ := E1f2 b + E3f2 b + E4f2 b

lemma hasDerivAt_Eb {b : ℝ} (hbb : b ≤ 1) : HasDerivAt Eb (Eb1 b) b := by
  have h2 : HasDerivAt (fun t : ℝ => t*l2hi) l2hi b := by
    have h := (hasDerivAt_idf b).mul_const l2hi
    convert h using 1 <;> (first | rfl | (funext t; ring) | ring | done)
  have h := (((hasDerivAt_E1f b).add h2).add (hasDerivAt_E3f hbb)).add (hasDerivAt_E4f hbb)
  convert h using 1 <;> (first | rfl | (funext t; simp only [Eb, Pi.add_apply]; ring) | (simp only [Eb1]; ring) | ring | done)

lemma hasDerivAt_Eb1 {b : ℝ} (hbb : b ≤ 1) : HasDerivAt Eb1 (Eb2 b) b := by
  have h2 : HasDerivAt (fun _ : ℝ => l2hi) 0 b := hasDerivAt_const b l2hi
  have h := (((hasDerivAt_E1f1 b).add h2).add (hasDerivAt_E3f1 hbb)).add (hasDerivAt_E4f1 hbb)
  convert h using 1 <;> (first | rfl | (funext t; simp only [Eb1, Pi.add_apply]; ring) | (simp only [Eb2]; ring) | ring | done)

/-! ### Numeric auxiliary sums -/

lemma sum_pow_le_two {b : ℝ} (hb : (1:ℝ)/4 ≤ b) (hb2 : b ≤ 1/2) :
    (∑ k ∈ Finset.range 8, (1-2*b)^k) ≤ 2 := by
  have h0 : (0:ℝ) ≤ 1-2*b := by linarith
  have h1 : 1-2*b ≤ 1/2 := by linarith
  calc (∑ k ∈ Finset.range 8, (1-2*b)^k) ≤ ∑ k ∈ Finset.range 8, ((1:ℝ)/2)^k :=
        Finset.sum_le_sum (fun k _ => pow_le_pow_left₀ h0 h1 k)
    _ = 255/128 := by norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
    _ ≤ 2 := by norm_num

lemma sum_wpow_le_four {b : ℝ} (hb : (1:ℝ)/4 ≤ b) (hb2 : b ≤ 1/2) :
    (∑ k ∈ Finset.range 7, ((k:ℝ)+1)*(1-2*b)^k) ≤ 4 := by
  have h0 : (0:ℝ) ≤ 1-2*b := by linarith
  have h1 : 1-2*b ≤ 1/2 := by linarith
  have hc : ∀ k : ℕ, (0:ℝ) ≤ (k:ℝ)+1 := fun k => by positivity
  calc (∑ k ∈ Finset.range 7, ((k:ℝ)+1)*(1-2*b)^k)
      ≤ ∑ k ∈ Finset.range 7, ((k:ℝ)+1)*((1:ℝ)/2)^k :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 k) (hc k))
    _ = 247/64 := by norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
    _ ≤ 4 := by norm_num

lemma P1f2_lower {b : ℝ} (h1 : (1:ℝ)/4 ≤ b) (h2 : b ≤ 1/2) : -(1:ℝ) ≤ P1f2 b := by
  have hSb25 : (5/2:ℝ) ≤ Sb b := by
    simp only [Sb]; nlinarith [sq_nonneg (b-1), sq_nonneg (b-1/2)]
  have hSb3 : ((5/2:ℝ))^3 ≤ (Sb b)^3 := by
    apply pow_le_pow_left₀ (by norm_num) hSb25
  have hpoly : (128*b^3 - 771*b^2 + 774*b - 2 : ℝ) ≤ (833/4 : ℝ) := by
    nlinarith [h1, h2, sq_nonneg (b-1/4), pow_nonneg (by linarith : (0:ℝ) ≤ b) 3]
  have hkey : (108304247:ℝ)*(128*b^3 - 771*b^2 + 774*b - 2) ≤ 7500000000*(Sb b)^3 := by
    nlinarith [hSb3, hpoly]
  have hSb : (0:ℝ) < (Sb b)^3 := by have := Sb_pos b; positivity
  rw [P1f2, le_div_iff₀ hSb]
  nlinarith [hkey]

lemma neg_P2f2_le {b : ℝ} (h1 : (1:ℝ)/4 ≤ b) (h2 : b ≤ 1/2) : -P2f2 b ≤ 5 := by
  have ha0 : (0:ℝ) ≤ 1-2*b := by linarith
  have ha1 : 1-2*b ≤ 1/2 := by linarith
  have hb0 : (0:ℝ) < b := by linarith
  have hS1 : (0:ℝ) ≤ ∑ k ∈ Finset.range 8, 2*(1-2*b)^k :=
    Finset.sum_nonneg (fun k _ => by positivity)
  have hS2 : (0:ℝ) ≤ ∑ k ∈ Finset.range 7, 4*((k:ℝ)+1)*(1-2*b)^k :=
    Finset.sum_nonneg (fun k _ => by positivity)
  have hs2 : (∑ k ∈ Finset.range 7, ((k:ℝ)+1)*(1-2*b)^k) ≤ 4 := sum_wpow_le_four h1 h2
  have hS2b : (∑ k ∈ Finset.range 7, (4*((k:ℝ)+1))*(1-2*b)^k) ≤ 16 := by
    have he : (∑ k ∈ Finset.range 7, (4*((k:ℝ)+1))*(1-2*b)^k)
        = 4 * (∑ k ∈ Finset.range 7, ((k:ℝ)+1)*(1-2*b)^k) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k hk; ring
    rw [he]; linarith
  have hb3 : (1:ℝ)/(128*b^3) ≤ 1/2 := by
    have hb3' : ((1:ℝ)/4)^3 ≤ b^3 := pow_le_pow_left₀ (by norm_num) h1 3
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 128*b^3)]
    nlinarith [hb3']
  have hkey : -P2f2 b = -(∑ k ∈ Finset.range 8, 2*(1-2*b)^k)
      + b/2*(∑ k ∈ Finset.range 7, 4*((k:ℝ)+1)*(1-2*b)^k) + 1/(128*b^3) := by
    simp only [P2f2, dlogUb, d2logUb]
    ring
  rw [hkey]
  have hb0' : (0:ℝ) ≤ b := le_of_lt hb0
  have e1 : (0:ℝ) ≤ b/2*(∑ k ∈ Finset.range 7, 4*((k:ℝ)+1)*(1-2*b)^k) :=
    mul_nonneg (by linarith) hS2
  have e2 : b/2*(∑ k ∈ Finset.range 7, 4*((k:ℝ)+1)*(1-2*b)^k) ≤ (1/2)/2*16 := by
    have : b/2 ≤ (1:ℝ)/2/2 := by linarith
    nlinarith [hS2, e1, hb0']
  linarith [hS1, e2, hb3, e1]

lemma P3f2_nonneg {b : ℝ} (h1 : (1:ℝ)/4 ≤ b) : (0:ℝ) ≤ P3f2 b := by
  have ha : (0:ℝ) ≤ 512*b^4 + 24*b^2 - 1 := by nlinarith [h1, sq_nonneg b]
  have hb : (0:ℝ) ≤ b := by linarith
  rw [P3f2]
  exact div_nonneg (by positivity) (by positivity)

lemma neg_E1f2_le {b : ℝ} (h1 : (1:ℝ)/4 ≤ b) (h2 : b ≤ 1/2) : -E1f2 b ≤ 9 := by
  have ha0 : (0:ℝ) ≤ 1-2*b := by linarith
  have ha1 : 1-2*b ≤ 1/2 := by linarith
  have hb0 : (0:ℝ) ≤ b := by linarith
  have hS1 : (0:ℝ) ≤ ∑ k ∈ Finset.range 8, 2*(1-2*b)^k :=
    Finset.sum_nonneg (fun k _ => by positivity)
  have hS2 : (0:ℝ) ≤ ∑ k ∈ Finset.range 7, 4*((k:ℝ)+1)*(1-2*b)^k :=
    Finset.sum_nonneg (fun k _ => by positivity)
  have hs1 : (∑ k ∈ Finset.range 8, (1-2*b)^k) ≤ 2 := sum_pow_le_two h1 h2
  have hS1b : (∑ k ∈ Finset.range 8, (2:ℝ)*(1-2*b)^k) ≤ 4 := by
    have he : (∑ k ∈ Finset.range 8, (2:ℝ)*(1-2*b)^k)
        = 2 * (∑ k ∈ Finset.range 8, (1-2*b)^k) := by
      rw [Finset.mul_sum]
    rw [he]; linarith
  have h8 : (1-2*b)^8 ≤ ((1:ℝ)/2)^8 := pow_le_pow_left₀ ha0 ha1 8
  have h7 : (0:ℝ) ≤ (1-2*b)^7 := pow_nonneg ha0 7
  have hkey : -E1f2 b = 2*(∑ k ∈ Finset.range 8, 2*(1-2*b)^k) + 8*(1-2*b)^8
      - b*(∑ k ∈ Finset.range 7, 4*((k:ℝ)+1)*(1-2*b)^k) - b*(64*(1-2*b)^7) := by
    simp only [E1f2, dlogLb, d2logLb]
    ring
  rw [hkey]
  have e1 : (0:ℝ) ≤ b*(∑ k ∈ Finset.range 7, 4*((k:ℝ)+1)*(1-2*b)^k) := mul_nonneg hb0 hS2
  have e2 : (0:ℝ) ≤ b*(64*(1-2*b)^7) := by positivity
  have e3 : 8*(1-2*b)^8 ≤ 8*((1:ℝ)/2)^8 := by linarith
  linarith [hS1b, e1, e2, e3]

lemma E3f2_nonneg {b : ℝ} (h1 : (1:ℝ)/4 ≤ b) : (0:ℝ) ≤ E3f2 b := by
  have ha : (0:ℝ) ≤ 47*b-4 := by linarith
  rw [E3f2]
  exact div_nonneg (by positivity) (by positivity)

lemma E4f2_nonneg {b : ℝ} (h1 : (0:ℝ) ≤ b) : (0:ℝ) ≤ E4f2 b := by
  have ha : (0:ℝ) ≤ 3*b+4 := by linarith
  rw [E4f2]
  exact div_nonneg (by positivity) (by positivity)

lemma neg_Lb2_le {b : ℝ} (h1 : (1:ℝ)/4 ≤ b) (h2 : b ≤ 1/2) : -Lb2 b ≤ 6 := by
  have hA := P1f2_lower h1 h2
  have hB := neg_P2f2_le h1 h2
  have hC := P3f2_nonneg h1
  simp only [Lb2]
  linarith

lemma neg_Eb2_le {b : ℝ} (h1 : (1:ℝ)/4 ≤ b) (h2 : b ≤ 1/2) : -Eb2 b ≤ 10 := by
  have hb0 : (0:ℝ) < b := by linarith
  have hA := neg_E1f2_le h1 h2
  have hB := E3f2_nonneg h1
  have hC := E4f2_nonneg (le_of_lt hb0)
  simp only [Eb2]
  linarith

/-! ## E. Ingredient bounds on `[0,1/2]` (regions I and II) -/

lemma dl1_range_lo {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1/2) : 0 ≤ dl1 b ∧ dl1 b ≤ 1/2 := by
  have hQ : (0:ℝ) < 8*b^2-24*b+19 := Q1pos b
  constructor
  · rw [dl1]; exact div_nonneg (by linarith) hQ.le
  · rw [dl1, div_le_iff₀ hQ]
    nlinarith [sq_nonneg (8*b-10)]

lemma dl2_range_lo {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1/2) : 0 ≤ dl2 b ∧ dl2 b ≤ 1/2 := by
  have hQ : (0:ℝ) < 8*(1+b)^2+1 := Q2pos b
  constructor
  · rw [dl2]; exact div_nonneg (by linarith) hQ.le
  · rw [dl2, div_le_iff₀ hQ]
    nlinarith [sq_nonneg (16*(1+b)-4)]

lemma dlr_range_lo {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1/2) : 0 ≤ dlr b ∧ dlr b ≤ 1/2 := by
  have hQ : (0:ℝ) < 8*(2-b)^2+1 := Q3pos b
  constructor
  · rw [dlr]; exact div_nonneg (by linarith) hQ.le
  · rw [dlr, div_le_iff₀ hQ]
    nlinarith [sq_nonneg (16*(2-b)-4)]

lemma dd1_bounds_lo {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1/2) : 0 ≤ dd1 b ∧ dd1 b ≤ 1/2 := by
  have hQ : (0:ℝ) < 8*b^2-24*b+19 := Q1pos b
  have hu : (0:ℝ) ≤ 8*b^2-24*b+17 := by nlinarith [sq_nonneg b, h0, h1]
  constructor
  · rw [dd1]; exact div_nonneg (by linarith) (pow_pos hQ 2).le
  · rw [dd1, div_le_iff₀ (pow_pos hQ 2)]
    nlinarith [sq_nonneg (8*b^2-24*b+17)]

lemma abs_d2d1_le_three {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1/2) : |d2d1 b| ≤ 3 := by
  have hQ : (0:ℝ) < 8*b^2-24*b+19 := Q1pos b
  have hQ9 : (9:ℝ) ≤ 8*b^2-24*b+19 := by nlinarith [sq_nonneg (b-1/2), h0, h1]
  have hQ19 : 8*b^2-24*b+19 ≤ 19 := by nlinarith [sq_nonneg b, h0, h1]
  have hid : d2d1 b = 2*(16*b-24)*(4-(8*b^2-24*b+19))/(8*b^2-24*b+19)^3 := by
    simp only [d2d1] <;> ring
  rw [hid]
  have hden : (0:ℝ) < (8*b^2-24*b+19)^3 := pow_pos hQ 3
  have hnum0 : (0:ℝ) ≤ 2*(16*b-24)*(4-(8*b^2-24*b+19)) := by
    apply mul_nonneg_of_nonpos_of_nonpos
    · exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (by linarith)
    · linarith
  rw [abs_of_nonneg (div_nonneg hnum0 hden.le)]
  rw [div_le_iff₀ hden]
  have hA : 2*(16*b-24)*(4-(8*b^2-24*b+19)) ≤ 720 := by
    have e : 2*(16*b-24)*(4-(8*b^2-24*b+19)) = 2*(24-16*b)*((8*b^2-24*b+19)-4) := by ring
    rw [e]
    have h2 : (0:ℝ) ≤ 24-16*b := by linarith
    have h3 : (0:ℝ) ≤ (8*b^2-24*b+19)-4 := by linarith
    have h4 : 24-16*b ≤ 24 := by linarith
    have h5 : (8*b^2-24*b+19)-4 ≤ 15 := by linarith
    nlinarith [mul_le_mul h4 h5 h3 (by norm_num : (0:ℝ) ≤ 24)]
  have hB : (720:ℝ) ≤ 3*(8*b^2-24*b+19)^3 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 9) hQ9 3
    linarith
  linarith

lemma abs_dd2_le_half {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1/2) : |dd2 b| ≤ 1/2 := by
  have hQ : (0:ℝ) < 8*(1+b)^2+1 := Q2pos b
  have hv : (0:ℝ) ≤ 8*(1+b)^2-1 := by nlinarith [sq_nonneg b, h0]
  have hid : dd2 b = -2*(8*(1+b)^2-1)/(8*(1+b)^2+1)^2 := by simp only [dd2] <;> ring
  have hnn : (0:ℝ) ≤ 2*(8*(1+b)^2-1)/(8*(1+b)^2+1)^2 :=
    div_nonneg (by nlinarith [hv]) (pow_pos hQ 2).le
  rw [hid, show -2*(8*(1+b)^2-1)/(8*(1+b)^2+1)^2
        = -(2*(8*(1+b)^2-1)/(8*(1+b)^2+1)^2) by ring,
      abs_neg, abs_of_nonneg hnn, div_le_iff₀ (pow_pos hQ 2)]
  nlinarith [sq_nonneg (8*(1+b)^2-1)]

lemma abs_d2d2_le_one {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1/2) : |d2d2 b| ≤ 1 := by
  have hQ : (0:ℝ) < 8*(1+b)^2+1 := Q2pos b
  have hv : (0:ℝ) ≤ 8*(1+b)^2-3 := by nlinarith [sq_nonneg b, h0]
  have hid : d2d2 b = 32*(1+b)*(8*(1+b)^2-3)/(8*(1+b)^2+1)^3 := by
    simp only [d2d2] <;> ring
  have hnum : (0:ℝ) ≤ 32*(1+b)*(8*(1+b)^2-3) :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hv
  rw [hid, abs_of_nonneg (div_nonneg hnum (pow_pos hQ 3).le), div_le_iff₀ (pow_pos hQ 3)]
  have h1b : (1:ℝ)+b ≤ 3/2 := by linarith
  have h3 : (1+b)^3 ≤ (3/2)^3 := pow_le_pow_left₀ (by linarith) h1b 3
  have hnum2 : 32*(1+b)*(8*(1+b)^2-3) ≤ 720 := by
    have e : 32*(1+b)*(8*(1+b)^2-3) = 256*(1+b)^3 - 96*(1+b) := by ring
    rw [e]; nlinarith [h3, h1b]
  have hlow : (729:ℝ) ≤ (8*(1+b)^2+1)^3 := by
    have hq : (9:ℝ) ≤ 8*(1+b)^2+1 := by nlinarith [sq_nonneg b, h0]
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 9) hq 3
    linarith
  linarith

lemma abs_ddr_le_half {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1/2) : |ddr b| ≤ 1/2 := by
  have hQ : (0:ℝ) < 8*(2-b)^2+1 := Q3pos b
  have hv : (0:ℝ) ≤ 8*(2-b)^2-1 := by nlinarith [sq_nonneg (2-b), h1]
  have hid : ddr b = 2*(8*(2-b)^2-1)/(8*(2-b)^2+1)^2 := by simp only [ddr] <;> ring
  rw [hid, abs_of_nonneg (div_nonneg (by nlinarith [hv]) (pow_pos hQ 2).le),
    div_le_iff₀ (pow_pos hQ 2)]
  nlinarith [sq_nonneg (8*(2-b)^2-1)]

lemma abs_d2dr_le_one {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1/2) : |d2dr b| ≤ 1 := by
  have hQ : (0:ℝ) < 8*(2-b)^2+1 := Q3pos b
  have hv : (0:ℝ) ≤ 8*(2-b)^2-3 := by nlinarith [sq_nonneg (2-b), h1]
  have hid : d2dr b = 32*(2-b)*(8*(2-b)^2-3)/(8*(2-b)^2+1)^3 := by
    simp only [d2dr] <;> ring
  have hnum : (0:ℝ) ≤ 32*(2-b)*(8*(2-b)^2-3) :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hv
  rw [hid, abs_of_nonneg (div_nonneg hnum (pow_pos hQ 3).le), div_le_iff₀ (pow_pos hQ 3)]
  have hu2 : (2:ℝ)-b ≤ 2 := by linarith
  have hu32 : 8*(2-b)^2-3 ≤ 29 := by
    have h : (2-b)^2 ≤ 4 := by nlinarith [sq_nonneg (2-b), h1]
    linarith
  have hnum2 : 32*(2-b)*(8*(2-b)^2-3) ≤ 32*2*29 := by
    nlinarith [mul_le_mul hu2 hu32 hv (by norm_num : (0:ℝ) ≤ 2)]
  have hlow : (1856:ℝ) ≤ (8*(2-b)^2+1)^3 := by
    have hq : (19:ℝ) ≤ 8*(2-b)^2+1 := by nlinarith [sq_nonneg (2-b), h1]
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 19) hq 3
    linarith
  linarith

lemma ddr_nonneg_lo {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1/2) : 0 ≤ ddr b := by
  have hQ : (0:ℝ) < 8*(2-b)^2+1 := Q3pos b
  have hv : (0:ℝ) ≤ 8*(2-b)^2-1 := by nlinarith [sq_nonneg (2-b), h1]
  rw [ddr]
  exact div_nonneg (by linarith) (pow_pos hQ 2).le

lemma Ctot_nonneg_lo {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1/2) : 0 ≤ Ctot b := by
  have hpos : (0:ℝ) < 2-b := by linarith
  rw [Ctot_eq b hpos]
  simp only [Ctot1, Ctot2, Ctot3]
  have hu : (0:ℝ) ≤ 1-b := by linarith
  positivity

lemma Ctot_le_two_lo {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1/2) : Ctot b ≤ 2 := by
  have hpos : (0:ℝ) < 2-b := by linarith
  rw [Ctot_eq b hpos]
  simp only [Ctot1, Ctot2, Ctot3]
  have hu : (0:ℝ) ≤ 1-b := by linarith
  have hu1 : 1-b ≤ 1 := by linarith
  have hd : (3/2:ℝ) ≤ 2-b := by linarith
  have h1' : 2*(1-b)/(2-b) ≤ 4/3 := by
    rw [div_le_iff₀ hpos]
    nlinarith [hu, hu1, hd]
  have h2' : (1-b)^2/(2-b)^3 ≤ 8/27 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (2-b)^3)]
    have hb2 : (1-b)^2 ≤ 1 := by nlinarith [hu, hu1]
    have hb3 : (27:ℝ) ≤ 8*(2-b)^3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3/2) hd 3
      linarith
    nlinarith [hb2, hb3]
  have h3' : (3/2)*(1-b)^3/(2-b)^5 ≤ 96/1024 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (2-b)^5)]
    have hb3 : (1-b)^3 ≤ 1 := by nlinarith [hu, hu1]
    have hb5 : (243:ℝ) ≤ 32*(2-b)^5 := by
      have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3/2) hd 5
      linarith
    nlinarith [hb3, hb5]
  linarith

lemma d2Ctot_nonpos_lo {b : ℝ} (h2 : b ≤ 1) : d2Ctot b ≤ 0 := by
  have hpos : (0:ℝ) < 2-b := by linarith
  rw [d2Ctot_nice b hpos]
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith [sq_nonneg (1-b), pow_nonneg (by linarith : (0:ℝ) ≤ 1-b) 3,
      pow_nonneg (by linarith : (0:ℝ) ≤ 1-b) 4]
  · positivity

lemma abs_d2LAf_le_half {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1/2) : |d2LAf b| ≤ 1/2 := by
  have hb0 : (0:ℝ) ≤ b/2 := by linarith
  have hb1 : b/2 ≤ 1/4 := by linarith
  have hfun : d2LAf b = -∑ k ∈ Finset.range 10, (k:ℝ)*(b/2)^(k-1)/4 := rfl
  rw [hfun, abs_neg]
  have hterm : ∀ k ∈ Finset.range 10,
      (k:ℝ)*(b/2)^(k-1)/4 ≤ (k:ℝ)*((1:ℝ)/4)^(k-1)/4 := by
    intro k hk
    have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    have hpow : (b/2)^(k-1) ≤ ((1:ℝ)/4)^(k-1) := pow_le_pow_left₀ hb0 hb1 (k-1)
    have hpk : (0:ℝ) ≤ ((1:ℝ)/4)^(k-1) := pow_nonneg (by norm_num) _
    have hpk2 : (0:ℝ) ≤ (b/2)^(k-1) := pow_nonneg hb0 _
    nlinarith
  have hsum := Finset.sum_le_sum hterm
  have hnn : (0:ℝ) ≤ ∑ k ∈ Finset.range 10, (k:ℝ)*(b/2)^(k-1)/4 := by
    apply Finset.sum_nonneg
    intro k hk
    have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    have := pow_nonneg hb0 (k-1)
    positivity
  have hval : (∑ k ∈ Finset.range 10, (k:ℝ)*((1:ℝ)/4)^(k-1)/4) ≤ 1/2 := by
    norm_num [Finset.sum_range_succ]
  rw [abs_of_nonneg hnn]
  linarith

lemma I0f_bounds_lo {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1/2) : 0 ≤ I0f b ∧ I0f b ≤ 1/4 := by
  have h2b : (2:ℝ)-b = 1 + (1-b) := by ring
  constructor
  · rw [I0f]
    have h1' : 7/(768*(2-b)^2) ≤ 7/768 := by
      apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 7) (by norm_num : (0:ℝ) < 768)
      nlinarith [h1]
    linarith
  · rw [I0f]; have : 0 ≤ 7/(768*(2-b)^2) := by positivity
    linarith

lemma abs_dI0f_le {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1/2) : |dI0f b| ≤ 7/384 := by
  have hpos : (0:ℝ) < 384*(2-b)^3 := by
    have h : (0:ℝ) < 2-b := by linarith
    positivity
  have hid : dI0f b = (-7)/(384*(2-b)^3) := by simp only [dI0f] <;> ring
  have hneg : dI0f b ≤ 0 := by
    rw [hid]; exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hpos.le
  have h2 : (1:ℝ) ≤ (2-b)^3 := by
    have h : (1:ℝ) ≤ 2-b := by linarith
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) h 3
    simpa using this
  rw [abs_of_nonpos hneg, hid, neg_div, neg_neg, div_le_iff₀ hpos]
  nlinarith [h2]

lemma abs_d2I0f_le {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1/2) : |d2I0f b| ≤ 7/128 := by
  have hpos : (0:ℝ) < 128*(2-b)^4 := by
    have h : (0:ℝ) < 2-b := by linarith
    positivity
  have hid : d2I0f b = (-7)/(128*(2-b)^4) := by simp only [d2I0f] <;> ring
  have hneg : d2I0f b ≤ 0 := by
    rw [hid]; exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hpos.le
  have h2 : (1:ℝ) ≤ (2-b)^4 := by
    have h : (1:ℝ) ≤ 2-b := by linarith
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) h 4
    simpa using this
  rw [abs_of_nonpos hneg, hid, neg_div, neg_neg, div_le_iff₀ hpos]
  nlinarith [h2]

lemma P4poly2_le_lo {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1/2) : P4poly2 b ≤ 8 := by
  rw [P4poly2]
  nlinarith [h0, h1, sq_nonneg b, pow_nonneg h0 3]

lemma P5poly2_le_lo {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1/2) : P5poly2 b ≤ 3/10 := by
  rw [P5poly2]
  nlinarith [h0, h1, sq_nonneg b]



lemma d2Stuff1f_bounds_lo {b : ℝ} (h1 : (0:ℝ) ≤ b) (h2 : b ≤ 1/2) :
    -(1:ℝ)/50 ≤ d2Stuff1f b ∧ d2Stuff1f b ≤ 1/50 := by
  have hA : (1:ℝ) ≤ 2-b := by linarith
  have hA2 : (2-b) ≤ 2 := by linarith
  have hA0 : (0:ℝ) < 2-b := by linarith
  have hc1 : (0:ℝ) ≤ s1c1*6 := by norm_num [s1c1, l2lo]
  have hc2 : s1c2*20 ≤ 0 := by norm_num [s1c2]
  have hc3 : (0:ℝ) ≤ s1c3*42 := by norm_num [s1c3]
  have hc4 : s1c4*72 ≤ 0 := by norm_num [s1c4]
  have e4 : (1:ℝ) ≤ (2-b)^4 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hA 4; simpa using this
  have e6 : (1:ℝ) ≤ (2-b)^6 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hA 6; simpa using this
  have e8 : (1:ℝ) ≤ (2-b)^8 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hA 8; simpa using this
  have e10 : (1:ℝ) ≤ (2-b)^10 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hA 10; simpa using this
  have f4 : (2-b)^4 ≤ 16 := by
    have := pow_le_pow_left₀ hA0.le hA2 4; norm_num at this ⊢; exact this
  have f6 : (2-b)^6 ≤ 64 := by
    have := pow_le_pow_left₀ hA0.le hA2 6; norm_num at this ⊢; exact this
  have f8 : (2-b)^8 ≤ 256 := by
    have := pow_le_pow_left₀ hA0.le hA2 8; norm_num at this ⊢; exact this
  have f10 : (2-b)^10 ≤ 1024 := by
    have := pow_le_pow_left₀ hA0.le hA2 10; norm_num at this ⊢; exact this
  unfold d2Stuff1f
  constructor
  · have p1 : s1c1*6/16 ≤ s1c1*6/(2-b)^4 :=
      div_le_div_of_nonneg_left hc1 (by positivity : (0:ℝ) < (2-b)^4) f4
    have p2 : s1c2*20 ≤ s1c2*20/(2-b)^6 := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < (2-b)^6)]
      nlinarith [hc2, e6]
    have p3 : s1c3*42/256 ≤ s1c3*42/(2-b)^8 :=
      div_le_div_of_nonneg_left hc3 (by positivity : (0:ℝ) < (2-b)^8) f8
    have p4 : s1c4*72 ≤ s1c4*72/(2-b)^10 := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < (2-b)^10)]
      nlinarith [hc4, e10]
    have hnum : -(1:ℝ)/50 ≤ s1c1*6/16 + s1c2*20 + s1c3*42/256 + s1c4*72 := by
      norm_num [s1c1, s1c2, s1c3, s1c4, l2lo]
    linarith
  · have q1 : s1c1*6/(2-b)^4 ≤ s1c1*6 := div_le_self hc1 e4
    have q2 : s1c2*20/(2-b)^6 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hc2 (by positivity)
    have q3 : s1c3*42/(2-b)^8 ≤ s1c3*42 := div_le_self hc3 e8
    have q4 : s1c4*72/(2-b)^10 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hc4 (by positivity)
    have hnum : s1c1*6 + 0 + s1c3*42 + 0 ≤ (1:ℝ)/50 := by
      norm_num [s1c1, s1c3, l2lo]
    linarith


noncomputable def G1 (b : ℝ) : ℝ :=
  (13/5)*(psi7 (dl1 b) + psi7 (dl2 b)) + Ctot b * psi7 (dlr b) + P4poly b + P5poly b
    - LAf b * I0f b - stuff1f b - b*l2hi

noncomputable def G1_1 (b : ℝ) : ℝ :=
  (13/5)*((dpsi7 (dl1 b) * dd1 b) + (dpsi7 (dl2 b) * dd2 b))
    + (dCtot b * psi7 (dlr b) + Ctot b * (dpsi7 (dlr b) * ddr b))
    + P4poly1 b + P5poly1 b
    - (dLAf b * I0f b + LAf b * dI0f b) - dStuff1f b - l2hi

noncomputable def G1_2 (b : ℝ) : ℝ :=
  (13/5)*((d2psi7 (dl1 b) * (dd1 b)^2 + dpsi7 (dl1 b) * d2d1 b)
        + (d2psi7 (dl2 b) * (dd2 b)^2 + dpsi7 (dl2 b) * d2d2 b))
    + (d2Ctot b * psi7 (dlr b) + 2*(dCtot b * (dpsi7 (dlr b) * ddr b))
        + Ctot b * (d2psi7 (dlr b) * (ddr b)^2 + dpsi7 (dlr b) * d2dr b))
    + P4poly2 b + P5poly2 b
    - (d2LAf b * I0f b + 2*(dLAf b * dI0f b) + LAf b * d2I0f b) - d2Stuff1f b

lemma hasDerivAt_G1 (b : ℝ) (hb : (0:ℝ) < 2-b) : HasDerivAt G1 (G1_1 b) b := by
  have h12 : HasDerivAt (fun b : ℝ => psi7 (dl1 b) + psi7 (dl2 b))
      ((dpsi7 (dl1 b) * dd1 b) + (dpsi7 (dl2 b) * dd2 b)) b :=
    (hasDerivAt_psi7_dl1 b).add (hasDerivAt_psi7_dl2 b)
  have h1 : HasDerivAt (fun b : ℝ => (13/5)*(psi7 (dl1 b) + psi7 (dl2 b)))
      ((13/5)*((dpsi7 (dl1 b) * dd1 b) + (dpsi7 (dl2 b) * dd2 b))) b :=
    h12.const_mul (13/5)
  have h3 : HasDerivAt (fun b : ℝ => Ctot b * psi7 (dlr b))
      (dCtot b * psi7 (dlr b) + Ctot b * (dpsi7 (dlr b) * ddr b)) b := hasDerivAt_Ctot_psi7 b hb
  have h4 : HasDerivAt (fun b : ℝ => P4poly b) (P4poly1 b) b := hasDerivAt_P4poly b
  have h5 : HasDerivAt (fun b : ℝ => P5poly b) (P5poly1 b) b := hasDerivAt_P5poly b
  have h6 : HasDerivAt (fun b : ℝ => LAf b * I0f b) (dLAf b * I0f b + LAf b * dI0f b) b :=
    hasDerivAt_LAf_I0f b hb
  have h7 : HasDerivAt (fun b : ℝ => stuff1f b) (dStuff1f b) b := hasDerivAt_stuff1f b hb
  have h8 : HasDerivAt (fun b : ℝ => b*l2hi) l2hi b :=
    ((hasDerivAt_idf b).mul_const l2hi).congr_deriv (by ring)
  have h := (((((h1.add h3).add h4).add h5).sub h6).sub h7).sub h8
  have hgoal : HasDerivAt (fun b : ℝ => (13/5)*(psi7 (dl1 b) + psi7 (dl2 b)) + Ctot b * psi7 (dlr b)
      + P4poly b + P5poly b - LAf b * I0f b - stuff1f b - b*l2hi)
      ((13/5)*((dpsi7 (dl1 b) * dd1 b) + (dpsi7 (dl2 b) * dd2 b))
        + (dCtot b * psi7 (dlr b) + Ctot b * (dpsi7 (dlr b) * ddr b))
        + P4poly1 b + P5poly1 b
        - (dLAf b * I0f b + LAf b * dI0f b) - dStuff1f b - l2hi) b := h
  rw [show G1 = fun b : ℝ => (13/5)*(psi7 (dl1 b) + psi7 (dl2 b)) + Ctot b * psi7 (dlr b)
      + P4poly b + P5poly b - LAf b * I0f b - stuff1f b - b*l2hi from by unfold G1; hcl]
  exact hgoal.congr_deriv (by unfold G1_1; ring)

lemma hasDerivAt_G1_1 (b : ℝ) (hb : (0:ℝ) < 2-b) : HasDerivAt G1_1 (G1_2 b) b := by
  have h12 : HasDerivAt
      (fun b : ℝ => (dpsi7 (dl1 b) * dd1 b) + (dpsi7 (dl2 b) * dd2 b))
      ((d2psi7 (dl1 b) * (dd1 b)^2 + dpsi7 (dl1 b) * d2d1 b)
        + (d2psi7 (dl2 b) * (dd2 b)^2 + dpsi7 (dl2 b) * d2d2 b)) b :=
    (hasDerivAt_dpsi7_dl1 b).add (hasDerivAt_dpsi7_dl2 b)
  have h1 : HasDerivAt (fun b : ℝ => (13/5)*((dpsi7 (dl1 b) * dd1 b) + (dpsi7 (dl2 b) * dd2 b)))
      ((13/5)*((d2psi7 (dl1 b) * (dd1 b)^2 + dpsi7 (dl1 b) * d2d1 b)
        + (d2psi7 (dl2 b) * (dd2 b)^2 + dpsi7 (dl2 b) * d2d2 b))) b :=
    h12.const_mul (13/5)
  have h3 : HasDerivAt (fun b : ℝ => dCtot b * psi7 (dlr b) + Ctot b * (dpsi7 (dlr b) * ddr b))
      (d2Ctot b * psi7 (dlr b) + 2*(dCtot b * (dpsi7 (dlr b) * ddr b))
        + Ctot b * (d2psi7 (dlr b) * (ddr b)^2 + dpsi7 (dlr b) * d2dr b)) b :=
    hasDerivAt_Ctot_psi7' b hb
  have h4 : HasDerivAt (fun b : ℝ => P4poly1 b) (P4poly2 b) b := hasDerivAt_P4poly1 b
  have h5 : HasDerivAt (fun b : ℝ => P5poly1 b) (P5poly2 b) b := hasDerivAt_P5poly1 b
  have h6 : HasDerivAt (fun b : ℝ => dLAf b * I0f b + LAf b * dI0f b)
      (d2LAf b * I0f b + 2*(dLAf b * dI0f b) + LAf b * d2I0f b) b := hasDerivAt_LAf_I0f' b hb
  have h7 : HasDerivAt (fun b : ℝ => dStuff1f b) (d2Stuff1f b) b := hasDerivAt_dStuff1f b hb
  have h8 : HasDerivAt (fun _ : ℝ => l2hi) 0 b := hasDerivAt_const b l2hi
  have h := (((((h1.add h3).add h4).add h5).sub h6).sub h7).sub h8
  have hgoal : HasDerivAt (fun b : ℝ => (13/5)*((dpsi7 (dl1 b) * dd1 b) + (dpsi7 (dl2 b) * dd2 b))
      + (dCtot b * psi7 (dlr b) + Ctot b * (dpsi7 (dlr b) * ddr b))
      + P4poly1 b + P5poly1 b
      - (dLAf b * I0f b + LAf b * dI0f b) - dStuff1f b - l2hi)
      ((13/5)*((d2psi7 (dl1 b) * (dd1 b)^2 + dpsi7 (dl1 b) * d2d1 b)
        + (d2psi7 (dl2 b) * (dd2 b)^2 + dpsi7 (dl2 b) * d2d2 b))
      + (d2Ctot b * psi7 (dlr b) + 2*(dCtot b * (dpsi7 (dlr b) * ddr b))
        + Ctot b * (d2psi7 (dlr b) * (ddr b)^2 + dpsi7 (dlr b) * d2dr b))
      + P4poly2 b + P5poly2 b
      - (d2LAf b * I0f b + 2*(dLAf b * dI0f b) + LAf b * d2I0f b) - d2Stuff1f b - 0) b := h
  rw [show G1_1 = fun b : ℝ => (13/5)*((dpsi7 (dl1 b) * dd1 b) + (dpsi7 (dl2 b) * dd2 b))
      + (dCtot b * psi7 (dlr b) + Ctot b * (dpsi7 (dlr b) * ddr b))
      + P4poly1 b + P5poly1 b
      - (dLAf b * I0f b + LAf b * dI0f b) - dStuff1f b - l2hi from by unfold G1_1; hcl]
  exact hgoal.congr_deriv (by unfold G1_2; ring)

lemma G1_2_le {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1/2) : G1_2 b ≤ 25 := by
  obtain ⟨hdl1a, hdl1b⟩ := dl1_range_lo h0 h1
  obtain ⟨hdl2a, hdl2b⟩ := dl2_range_lo h0 h1
  obtain ⟨hdlra, hdlrb⟩ := dlr_range_lo h0 h1
  have t1 : (13/5)*((d2psi7 (dl1 b) * (dd1 b)^2 + dpsi7 (dl1 b) * d2d1 b)
        + (d2psi7 (dl2 b) * (dd2 b)^2 + dpsi7 (dl2 b) * d2d2 b)) ≤ 13 := by
    have hB1 : |d2psi7 (dl1 b)| ≤ 2 := abs_d2psi7_le_two hdl1a hdl1b
    have hB1' : |dpsi7 (dl1 b)| ≤ 1 := abs_dpsi7_le_one hdl1a (by linarith)
    have hB2 : |d2psi7 (dl2 b)| ≤ 2 := abs_d2psi7_le_two hdl2a hdl2b
    have hB2' : |dpsi7 (dl2 b)| ≤ 1 := abs_dpsi7_le_one hdl2a (by linarith)
    obtain ⟨hdd1a, hdd1b⟩ := dd1_bounds_lo h0 h1
    have hdd2 : |dd2 b| ≤ 1/2 := abs_dd2_le_half h0 h1
    have hd2d1 : |d2d1 b| ≤ 3 := abs_d2d1_le_three h0 h1
    have hd2d2 : |d2d2 b| ≤ 1 := abs_d2d2_le_one h0 h1
    have ha : d2psi7 (dl1 b) * (dd1 b)^2 ≤ 2*(1/2)^2 :=
      mul_le_of_abs_le hB1 (abs_sq_le_sq (abs_le.mpr ⟨by linarith, hdd1b⟩))
    have hb : dpsi7 (dl1 b) * d2d1 b ≤ 1*3 := mul_le_of_abs_le hB1' hd2d1
    have hc : d2psi7 (dl2 b) * (dd2 b)^2 ≤ 2*(1/2)^2 :=
      mul_le_of_abs_le hB2 (abs_sq_le_sq hdd2)
    have hd : dpsi7 (dl2 b) * d2d2 b ≤ 1*1 := mul_le_of_abs_le hB2' hd2d2
    have hsum : (d2psi7 (dl1 b) * (dd1 b)^2 + dpsi7 (dl1 b) * d2d1 b)
        + (d2psi7 (dl2 b) * (dd2 b)^2 + dpsi7 (dl2 b) * d2d2 b) ≤ 5 := by linarith
    nlinarith [hsum]
  have t3 : d2Ctot b * psi7 (dlr b) + 2*(dCtot b * (dpsi7 (dlr b) * ddr b))
      + Ctot b * (d2psi7 (dlr b) * (ddr b)^2 + dpsi7 (dlr b) * d2dr b) ≤ 3 := by
    have hCt0 : 0 ≤ Ctot b := Ctot_nonneg_lo h0 h1
    have hCt2 : Ctot b ≤ 2 := Ctot_le_two_lo h0 h1
    have hdCt : dCtot b ≤ 0 := dCtot_nonpos (by linarith : b ≤ 1)
    have hd2Ct : d2Ctot b ≤ 0 := d2Ctot_nonpos_lo (by linarith : b ≤ 1)
    have hpsi : 0 ≤ psi7 (dlr b) := (psi7_range hdlra (by linarith)).1
    have hdpsi : 0 ≤ dpsi7 (dlr b) := dpsi7_nonneg hdlra (by linarith)
    have hddr0 : 0 ≤ ddr b := ddr_nonneg_lo h0 h1
    have h1' : d2Ctot b * psi7 (dlr b) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hd2Ct hpsi
    have h2' : dCtot b * (dpsi7 (dlr b) * ddr b) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hdCt (mul_nonneg hdpsi hddr0)
    have hR2 : |d2psi7 (dlr b)| ≤ 2 := abs_d2psi7_le_two hdlra hdlrb
    have hR1 : |dpsi7 (dlr b)| ≤ 1 := abs_dpsi7_le_one hdlra (by linarith)
    have hddr : |ddr b| ≤ 1/2 := abs_ddr_le_half h0 h1
    have hd2dr : |d2dr b| ≤ 1 := abs_d2dr_le_one h0 h1
    have h3a : d2psi7 (dlr b) * (ddr b)^2 ≤ 2*(1/2)^2 := mul_le_of_abs_le hR2 (abs_sq_le_sq hddr)
    have h3b : dpsi7 (dlr b) * d2dr b ≤ 1*1 := mul_le_of_abs_le hR1 hd2dr
    have h3c : d2psi7 (dlr b) * (ddr b)^2 + dpsi7 (dlr b) * d2dr b ≤ 3/2 := by linarith
    by_cases hp : 0 ≤ d2psi7 (dlr b) * (ddr b)^2 + dpsi7 (dlr b) * d2dr b
    · have hm := mul_le_mul hCt2 h3c hp (by norm_num : (0:ℝ) ≤ 2)
      linarith
    · have hn : d2psi7 (dlr b) * (ddr b)^2 + dpsi7 (dlr b) * d2dr b ≤ 0 := by linarith
      have hm : Ctot b * (d2psi7 (dlr b) * (ddr b)^2 + dpsi7 (dlr b) * d2dr b) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hCt0 hn
      linarith
  have t6 : -(d2LAf b * I0f b + 2*(dLAf b * dI0f b) + LAf b * d2I0f b) ≤ 13/48 := by
    have hI0 : 0 ≤ I0f b ∧ I0f b ≤ 1/4 := I0f_bounds_lo h0 h1
    have hLA : 0 ≤ LAf b ∧ LAf b ≤ 2 := LAf_bounds2 h0 (by linarith : b ≤ 1)
    have hdLA1 : dLAf b ≤ 0 := (LAf_bounds h0 (by linarith : b ≤ 1)).2.1
    have hdLA2 : -1 ≤ dLAf b := dLAf_ge h0 (by linarith : b ≤ 1)
    have hd2LA : |d2LAf b| ≤ 1/2 := abs_d2LAf_le_half h0 h1
    have hdI0 : |dI0f b| ≤ 7/384 := abs_dI0f_le h0 h1
    have hd2I0 : |d2I0f b| ≤ 7/128 := abs_d2I0f_le h0 h1
    have habs1 : |d2LAf b * I0f b| ≤ (1/2)*(1/4) :=
      abs_mul_le hd2LA (abs_le.mpr ⟨by linarith, hI0.2⟩)
    have habs2 : |dLAf b * dI0f b| ≤ 1*(7/384) :=
      abs_mul_le (abs_le.mpr ⟨hdLA2, by linarith⟩) hdI0
    have habs3 : |LAf b * d2I0f b| ≤ 2*(7/128) :=
      abs_mul_le (abs_le.mpr ⟨by linarith, hLA.2⟩) hd2I0
    linarith [neg_abs_le (d2LAf b * I0f b), neg_abs_le (dLAf b * dI0f b),
      neg_abs_le (LAf b * d2I0f b)]
  have t9 : -d2Stuff1f b ≤ 1/50 := by
    have := (d2Stuff1f_bounds_lo h0 h1).1
    linarith
  have hP4 : P4poly2 b ≤ 8 := P4poly2_le_lo h0 h1
  have hP5 : P5poly2 b ≤ 3/10 := P5poly2_le_lo h0 h1
  rw [G1_2]
  linarith only [t1, t3, t6, t9, hP4, hP5]

noncomputable def Gh (b : ℝ) : ℝ := G1 b + b*l2hi - Lb b - Eb b
noncomputable def Gh1 (b : ℝ) : ℝ := G1_1 b + l2hi - Lb1 b - Eb1 b
noncomputable def Gh2 (b : ℝ) : ℝ := G1_2 b - Lb2 b - Eb2 b

lemma hasDerivAt_Gh {b : ℝ} (hb0 : b ≠ 0) (hbb : b ≤ 1) (hb : (0:ℝ) < 2-b) :
    HasDerivAt Gh (Gh1 b) b := by
  have h1 : HasDerivAt G1 (G1_1 b) b := hasDerivAt_G1 b hb
  have h8 : HasDerivAt (fun b : ℝ => b*l2hi) l2hi b :=
    ((hasDerivAt_idf b).mul_const l2hi).congr_deriv (by ring)
  have hL : HasDerivAt Lb (Lb1 b) b := hasDerivAt_Lb hb0
  have hE : HasDerivAt Eb (Eb1 b) b := hasDerivAt_Eb hbb
  have h := ((h1.add h8).sub hL).sub hE
  convert h using 1 <;> (first | (unfold Gh; hcl) | (unfold Gh1; hcl) | hcl)

lemma hasDerivAt_Gh1 {b : ℝ} (hb0 : b ≠ 0) (hbb : b ≤ 1) (hb : (0:ℝ) < 2-b) :
    HasDerivAt Gh1 (Gh2 b) b := by
  have h1 : HasDerivAt G1_1 (G1_2 b) b := hasDerivAt_G1_1 b hb
  have h8 : HasDerivAt (fun _ : ℝ => l2hi) 0 b := hasDerivAt_const b l2hi
  have hL : HasDerivAt Lb1 (Lb2 b) b := hasDerivAt_Lb1 hb0
  have hE : HasDerivAt Eb1 (Eb2 b) b := hasDerivAt_Eb1 hbb
  have h := ((h1.add h8).sub hL).sub hE
  convert h using 1 <;> (first | (unfold Gh1; hcl) | (unfold Gh2; hcl) | hcl)

lemma Gh2_le {b : ℝ} (h0 : (1:ℝ)/4 ≤ b) (h1 : b ≤ 1/2) : Gh2 b ≤ 45 := by
  have hg : G1_2 b ≤ 25 := G1_2_le (by linarith) h1
  have hl : -Lb2 b ≤ 6 := neg_Lb2_le h0 h1
  have he : -Eb2 b ≤ 10 := neg_Eb2_le h0 h1
  rw [Gh2]; linarith

/-! ## G. Chord assembly: `3/10 ≤ G1 b` on `[0,1/4]` and `3/10 ≤ Gh b` on `[1/4,1/2]` -/

lemma chord_block_g {f f' f'' : ℝ → ℝ} {c d M : ℝ} (hcd : c < d) (hM : 0 ≤ M)
    (hf : ∀ x ∈ Set.Icc c d, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc c d, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x ∈ Set.Icc c d, f'' x ≤ M)
    (hc0 : (3:ℝ)/10 + M*(d-c)^2/8 ≤ f c) (hd0 : (3:ℝ)/10 + M*(d-c)^2/8 ≤ f d) :
    ∀ β ∈ Set.Icc c d, (3:ℝ)/10 ≤ f β := by
  intro β hβ
  have h := chord_lower hcd hf hf' hf'' β hβ
  have hquad : M*(β-c)*(d-β)/2 ≤ M*(d-c)^2/8 := by
    have hq : (β-c)*(d-β) ≤ (d-c)^2/4 := by nlinarith [sq_nonneg (2*β-c-d)]
    nlinarith [hq, hM]
  have h1 : 0 ≤ (d-β)/(d-c) := div_nonneg (by linarith [hβ.2]) (by linarith)
  have h2 : 0 ≤ (β-c)/(d-c) := div_nonneg (by linarith [hβ.1]) (by linarith)
  have h3 : (d-β)/(d-c) + (β-c)/(d-c) = 1 := by
    have hdc : (d-c) ≠ 0 := by linarith
    have hsum2 : (d-β) + (β-c) = d-c := by ring
    rw [← add_div, hsum2, div_self hdc]
  have hkey : (3:ℝ)/10 + M*(d-c)^2/8 ≤ ((d-β)/(d-c))*f c + ((β-c)/(d-c))*f d := by
    have ha := mul_le_mul_of_nonneg_left hc0 h1
    have hb := mul_le_mul_of_nonneg_left hd0 h2
    have hsum : ((d-β)/(d-c))*((3:ℝ)/10 + M*(d-c)^2/8) + ((β-c)/(d-c))*((3:ℝ)/10 + M*(d-c)^2/8)
        = (3:ℝ)/10 + M*(d-c)^2/8 := by rw [← add_mul, h3, one_mul]
    calc (3:ℝ)/10 + M*(d-c)^2/8
        = ((d-β)/(d-c))*((3:ℝ)/10 + M*(d-c)^2/8) + ((β-c)/(d-c))*((3:ℝ)/10 + M*(d-c)^2/8) := hsum.symm
      _ ≤ ((d-β)/(d-c))*f c + ((β-c)/(d-c))*f d := add_le_add ha hb
  have hcomb : ((d-β)*f c + (β-c)*f d)/(d-c) = ((d-β)/(d-c))*f c + ((β-c)/(d-c))*f d := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
  rw [hcomb] at h
  linarith

lemma G1_node (i : ℕ) (hi : i ≤ 16) :
    (3:ℝ)/10 + 25/32768 ≤ G1 (i/64) := by
  interval_cases i <;>
    norm_num [G1, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, I0f, stuff1f, K1pf, l2lo, l2hi]

lemma Gh_node (i : ℕ) (hi : i ≤ 16) :
    (3:ℝ)/10 + 45/32768 ≤ Gh ((1:ℝ)/4 + i/64) := by
  interval_cases i <;>
    norm_num [Gh, G1, psi7, dl1, dl2, dlr, Ctot, P4poly, P5poly, LAf, I0f, stuff1f, K1pf,
      Lb, P1f, P2f, P3f, Eb, E1f, E3f, E4f, logUb, logLb, rhof, Sb, l2lo, l2hi]

theorem G1_ge {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1/4) : (3:ℝ)/10 ≤ G1 b := by
  have hD1 : ∀ x ∈ Set.Icc (0:ℝ) (1/4), HasDerivAt G1 (G1_1 x) x :=
    fun x hx => hasDerivAt_G1 x (by linarith [hx.2])
  have hD2 : ∀ x ∈ Set.Icc (0:ℝ) (1/4), HasDerivAt G1_1 (G1_2 x) x :=
    fun x hx => hasDerivAt_G1_1 x (by linarith [hx.2])
  have hD3 : ∀ x ∈ Set.Icc (0:ℝ) (1/4), G1_2 x ≤ 25 := fun x hx => G1_2_le hx.1 (by linarith [hx.2])
  by_cases hb1 : b ≤ (1/64:ℝ)
  ·
    exact chord_block_g (c := ((0/64:ℝ):ℝ)) (d := ((1/64:ℝ):ℝ)) (M := 25) (by norm_num) (by norm_num)
      (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      (by have := G1_node 0 (by norm_num); linarith)
      (by have := G1_node 1 (by norm_num); linarith)
      b ⟨by linarith, hb1⟩
  ·
    by_cases hb2 : b ≤ (2/64:ℝ)
    ·
      exact chord_block_g (c := ((1/64:ℝ):ℝ)) (d := ((2/64:ℝ):ℝ)) (M := 25) (by norm_num) (by norm_num)
        (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
        (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
        (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
        (by have := G1_node 1 (by norm_num); linarith)
        (by have := G1_node 2 (by norm_num); linarith)
        b ⟨by linarith, hb2⟩
    ·
      by_cases hb3 : b ≤ (3/64:ℝ)
      ·
        exact chord_block_g (c := ((2/64:ℝ):ℝ)) (d := ((3/64:ℝ):ℝ)) (M := 25) (by norm_num) (by norm_num)
          (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
          (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
          (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
          (by have := G1_node 2 (by norm_num); linarith)
          (by have := G1_node 3 (by norm_num); linarith)
          b ⟨by linarith, hb3⟩
      ·
        by_cases hb4 : b ≤ (4/64:ℝ)
        ·
          exact chord_block_g (c := ((3/64:ℝ):ℝ)) (d := ((4/64:ℝ):ℝ)) (M := 25) (by norm_num) (by norm_num)
            (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
            (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
            (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
            (by have := G1_node 3 (by norm_num); linarith)
            (by have := G1_node 4 (by norm_num); linarith)
            b ⟨by linarith, hb4⟩
        ·
          by_cases hb5 : b ≤ (5/64:ℝ)
          ·
            exact chord_block_g (c := ((4/64:ℝ):ℝ)) (d := ((5/64:ℝ):ℝ)) (M := 25) (by norm_num) (by norm_num)
              (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
              (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
              (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
              (by have := G1_node 4 (by norm_num); linarith)
              (by have := G1_node 5 (by norm_num); linarith)
              b ⟨by linarith, hb5⟩
          ·
            by_cases hb6 : b ≤ (6/64:ℝ)
            ·
              exact chord_block_g (c := ((5/64:ℝ):ℝ)) (d := ((6/64:ℝ):ℝ)) (M := 25) (by norm_num) (by norm_num)
                (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                (by have := G1_node 5 (by norm_num); linarith)
                (by have := G1_node 6 (by norm_num); linarith)
                b ⟨by linarith, hb6⟩
            ·
              by_cases hb7 : b ≤ (7/64:ℝ)
              ·
                exact chord_block_g (c := ((6/64:ℝ):ℝ)) (d := ((7/64:ℝ):ℝ)) (M := 25) (by norm_num) (by norm_num)
                  (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                  (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                  (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                  (by have := G1_node 6 (by norm_num); linarith)
                  (by have := G1_node 7 (by norm_num); linarith)
                  b ⟨by linarith, hb7⟩
              ·
                by_cases hb8 : b ≤ (8/64:ℝ)
                ·
                  exact chord_block_g (c := ((7/64:ℝ):ℝ)) (d := ((8/64:ℝ):ℝ)) (M := 25) (by norm_num) (by norm_num)
                    (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                    (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                    (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                    (by have := G1_node 7 (by norm_num); linarith)
                    (by have := G1_node 8 (by norm_num); linarith)
                    b ⟨by linarith, hb8⟩
                ·
                  by_cases hb9 : b ≤ (9/64:ℝ)
                  ·
                    exact chord_block_g (c := ((8/64:ℝ):ℝ)) (d := ((9/64:ℝ):ℝ)) (M := 25) (by norm_num) (by norm_num)
                      (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                      (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                      (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                      (by have := G1_node 8 (by norm_num); linarith)
                      (by have := G1_node 9 (by norm_num); linarith)
                      b ⟨by linarith, hb9⟩
                  ·
                    by_cases hb10 : b ≤ (10/64:ℝ)
                    ·
                      exact chord_block_g (c := ((9/64:ℝ):ℝ)) (d := ((10/64:ℝ):ℝ)) (M := 25) (by norm_num) (by norm_num)
                        (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                        (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                        (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                        (by have := G1_node 9 (by norm_num); linarith)
                        (by have := G1_node 10 (by norm_num); linarith)
                        b ⟨by linarith, hb10⟩
                    ·
                      by_cases hb11 : b ≤ (11/64:ℝ)
                      ·
                        exact chord_block_g (c := ((10/64:ℝ):ℝ)) (d := ((11/64:ℝ):ℝ)) (M := 25) (by norm_num) (by norm_num)
                          (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                          (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                          (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                          (by have := G1_node 10 (by norm_num); linarith)
                          (by have := G1_node 11 (by norm_num); linarith)
                          b ⟨by linarith, hb11⟩
                      ·
                        by_cases hb12 : b ≤ (12/64:ℝ)
                        ·
                          exact chord_block_g (c := ((11/64:ℝ):ℝ)) (d := ((12/64:ℝ):ℝ)) (M := 25) (by norm_num) (by norm_num)
                            (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                            (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                            (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                            (by have := G1_node 11 (by norm_num); linarith)
                            (by have := G1_node 12 (by norm_num); linarith)
                            b ⟨by linarith, hb12⟩
                        ·
                          by_cases hb13 : b ≤ (13/64:ℝ)
                          ·
                            exact chord_block_g (c := ((12/64:ℝ):ℝ)) (d := ((13/64:ℝ):ℝ)) (M := 25) (by norm_num) (by norm_num)
                              (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                              (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                              (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                              (by have := G1_node 12 (by norm_num); linarith)
                              (by have := G1_node 13 (by norm_num); linarith)
                              b ⟨by linarith, hb13⟩
                          ·
                            by_cases hb14 : b ≤ (14/64:ℝ)
                            ·
                              exact chord_block_g (c := ((13/64:ℝ):ℝ)) (d := ((14/64:ℝ):ℝ)) (M := 25) (by norm_num) (by norm_num)
                                (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                                (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                                (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                                (by have := G1_node 13 (by norm_num); linarith)
                                (by have := G1_node 14 (by norm_num); linarith)
                                b ⟨by linarith, hb14⟩
                            ·
                              by_cases hb15 : b ≤ (15/64:ℝ)
                              ·
                                exact chord_block_g (c := ((14/64:ℝ):ℝ)) (d := ((15/64:ℝ):ℝ)) (M := 25) (by norm_num) (by norm_num)
                                  (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                                  (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                                  (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                                  (by have := G1_node 14 (by norm_num); linarith)
                                  (by have := G1_node 15 (by norm_num); linarith)
                                  b ⟨by linarith, hb15⟩
                              ·
                                  exact chord_block_g (c := ((15/64:ℝ):ℝ)) (d := ((16/64:ℝ):ℝ)) (M := 25) (by norm_num) (by norm_num)
                                    (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                                    (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                                    (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                                    (by have := G1_node 15 (by norm_num); linarith)
                                    (by have := G1_node 16 (by norm_num); linarith)
                                    b ⟨by linarith, by linarith⟩

theorem Gh_ge {b : ℝ} (h0 : (1:ℝ)/4 ≤ b) (h1 : b ≤ 1/2) : (3:ℝ)/10 ≤ Gh b := by
  have hD1 : ∀ x ∈ Set.Icc (1/4:ℝ) (1/2), HasDerivAt Gh (Gh1 x) x :=
    fun x hx => hasDerivAt_Gh (by linarith [hx.1]) (by linarith [hx.2]) (by linarith [hx.2])
  have hD2 : ∀ x ∈ Set.Icc (1/4:ℝ) (1/2), HasDerivAt Gh1 (Gh2 x) x :=
    fun x hx => hasDerivAt_Gh1 (by linarith [hx.1]) (by linarith [hx.2]) (by linarith [hx.2])
  have hD3 : ∀ x ∈ Set.Icc (1/4:ℝ) (1/2), Gh2 x ≤ 45 := fun x hx => Gh2_le hx.1 hx.2
  by_cases hb1 : b ≤ ((1:ℝ)/4 + 1/64)
  ·
    exact chord_block_g (c := (((1:ℝ)/4 + 0/64):ℝ)) (d := (((1:ℝ)/4 + 1/64):ℝ)) (M := 45) (by norm_num) (by norm_num)
      (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      (by have := Gh_node 0 (by norm_num); linarith)
      (by have := Gh_node 1 (by norm_num); linarith)
      b ⟨by linarith, hb1⟩
  ·
    by_cases hb2 : b ≤ ((1:ℝ)/4 + 2/64)
    ·
      exact chord_block_g (c := (((1:ℝ)/4 + 1/64):ℝ)) (d := (((1:ℝ)/4 + 2/64):ℝ)) (M := 45) (by norm_num) (by norm_num)
        (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
        (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
        (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
        (by have := Gh_node 1 (by norm_num); linarith)
        (by have := Gh_node 2 (by norm_num); linarith)
        b ⟨by linarith, hb2⟩
    ·
      by_cases hb3 : b ≤ ((1:ℝ)/4 + 3/64)
      ·
        exact chord_block_g (c := (((1:ℝ)/4 + 2/64):ℝ)) (d := (((1:ℝ)/4 + 3/64):ℝ)) (M := 45) (by norm_num) (by norm_num)
          (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
          (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
          (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
          (by have := Gh_node 2 (by norm_num); linarith)
          (by have := Gh_node 3 (by norm_num); linarith)
          b ⟨by linarith, hb3⟩
      ·
        by_cases hb4 : b ≤ ((1:ℝ)/4 + 4/64)
        ·
          exact chord_block_g (c := (((1:ℝ)/4 + 3/64):ℝ)) (d := (((1:ℝ)/4 + 4/64):ℝ)) (M := 45) (by norm_num) (by norm_num)
            (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
            (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
            (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
            (by have := Gh_node 3 (by norm_num); linarith)
            (by have := Gh_node 4 (by norm_num); linarith)
            b ⟨by linarith, hb4⟩
        ·
          by_cases hb5 : b ≤ ((1:ℝ)/4 + 5/64)
          ·
            exact chord_block_g (c := (((1:ℝ)/4 + 4/64):ℝ)) (d := (((1:ℝ)/4 + 5/64):ℝ)) (M := 45) (by norm_num) (by norm_num)
              (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
              (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
              (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
              (by have := Gh_node 4 (by norm_num); linarith)
              (by have := Gh_node 5 (by norm_num); linarith)
              b ⟨by linarith, hb5⟩
          ·
            by_cases hb6 : b ≤ ((1:ℝ)/4 + 6/64)
            ·
              exact chord_block_g (c := (((1:ℝ)/4 + 5/64):ℝ)) (d := (((1:ℝ)/4 + 6/64):ℝ)) (M := 45) (by norm_num) (by norm_num)
                (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                (by have := Gh_node 5 (by norm_num); linarith)
                (by have := Gh_node 6 (by norm_num); linarith)
                b ⟨by linarith, hb6⟩
            ·
              by_cases hb7 : b ≤ ((1:ℝ)/4 + 7/64)
              ·
                exact chord_block_g (c := (((1:ℝ)/4 + 6/64):ℝ)) (d := (((1:ℝ)/4 + 7/64):ℝ)) (M := 45) (by norm_num) (by norm_num)
                  (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                  (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                  (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                  (by have := Gh_node 6 (by norm_num); linarith)
                  (by have := Gh_node 7 (by norm_num); linarith)
                  b ⟨by linarith, hb7⟩
              ·
                by_cases hb8 : b ≤ ((1:ℝ)/4 + 8/64)
                ·
                  exact chord_block_g (c := (((1:ℝ)/4 + 7/64):ℝ)) (d := (((1:ℝ)/4 + 8/64):ℝ)) (M := 45) (by norm_num) (by norm_num)
                    (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                    (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                    (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                    (by have := Gh_node 7 (by norm_num); linarith)
                    (by have := Gh_node 8 (by norm_num); linarith)
                    b ⟨by linarith, hb8⟩
                ·
                  by_cases hb9 : b ≤ ((1:ℝ)/4 + 9/64)
                  ·
                    exact chord_block_g (c := (((1:ℝ)/4 + 8/64):ℝ)) (d := (((1:ℝ)/4 + 9/64):ℝ)) (M := 45) (by norm_num) (by norm_num)
                      (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                      (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                      (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                      (by have := Gh_node 8 (by norm_num); linarith)
                      (by have := Gh_node 9 (by norm_num); linarith)
                      b ⟨by linarith, hb9⟩
                  ·
                    by_cases hb10 : b ≤ ((1:ℝ)/4 + 10/64)
                    ·
                      exact chord_block_g (c := (((1:ℝ)/4 + 9/64):ℝ)) (d := (((1:ℝ)/4 + 10/64):ℝ)) (M := 45) (by norm_num) (by norm_num)
                        (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                        (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                        (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                        (by have := Gh_node 9 (by norm_num); linarith)
                        (by have := Gh_node 10 (by norm_num); linarith)
                        b ⟨by linarith, hb10⟩
                    ·
                      by_cases hb11 : b ≤ ((1:ℝ)/4 + 11/64)
                      ·
                        exact chord_block_g (c := (((1:ℝ)/4 + 10/64):ℝ)) (d := (((1:ℝ)/4 + 11/64):ℝ)) (M := 45) (by norm_num) (by norm_num)
                          (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                          (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                          (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                          (by have := Gh_node 10 (by norm_num); linarith)
                          (by have := Gh_node 11 (by norm_num); linarith)
                          b ⟨by linarith, hb11⟩
                      ·
                        by_cases hb12 : b ≤ ((1:ℝ)/4 + 12/64)
                        ·
                          exact chord_block_g (c := (((1:ℝ)/4 + 11/64):ℝ)) (d := (((1:ℝ)/4 + 12/64):ℝ)) (M := 45) (by norm_num) (by norm_num)
                            (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                            (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                            (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                            (by have := Gh_node 11 (by norm_num); linarith)
                            (by have := Gh_node 12 (by norm_num); linarith)
                            b ⟨by linarith, hb12⟩
                        ·
                          by_cases hb13 : b ≤ ((1:ℝ)/4 + 13/64)
                          ·
                            exact chord_block_g (c := (((1:ℝ)/4 + 12/64):ℝ)) (d := (((1:ℝ)/4 + 13/64):ℝ)) (M := 45) (by norm_num) (by norm_num)
                              (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                              (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                              (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                              (by have := Gh_node 12 (by norm_num); linarith)
                              (by have := Gh_node 13 (by norm_num); linarith)
                              b ⟨by linarith, hb13⟩
                          ·
                            by_cases hb14 : b ≤ ((1:ℝ)/4 + 14/64)
                            ·
                              exact chord_block_g (c := (((1:ℝ)/4 + 13/64):ℝ)) (d := (((1:ℝ)/4 + 14/64):ℝ)) (M := 45) (by norm_num) (by norm_num)
                                (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                                (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                                (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                                (by have := Gh_node 13 (by norm_num); linarith)
                                (by have := Gh_node 14 (by norm_num); linarith)
                                b ⟨by linarith, hb14⟩
                            ·
                              by_cases hb15 : b ≤ ((1:ℝ)/4 + 15/64)
                              ·
                                exact chord_block_g (c := (((1:ℝ)/4 + 14/64):ℝ)) (d := (((1:ℝ)/4 + 15/64):ℝ)) (M := 45) (by norm_num) (by norm_num)
                                  (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                                  (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                                  (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                                  (by have := Gh_node 14 (by norm_num); linarith)
                                  (by have := Gh_node 15 (by norm_num); linarith)
                                  b ⟨by linarith, hb15⟩
                              ·
                                  exact chord_block_g (c := (((1:ℝ)/4 + 15/64):ℝ)) (d := (((1:ℝ)/4 + 16/64):ℝ)) (M := 45) (by norm_num) (by norm_num)
                                    (fun x hx => hD1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                                    (fun x hx => hD2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                                    (fun x hx => hD3 x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
                                    (by have := Gh_node 15 (by norm_num); linarith)
                                    (by have := Gh_node 16 (by norm_num); linarith)
                                    b ⟨by linarith, by linarith⟩

/-! ## H. Analytic lemmas and integral evaluations -/

theorem log_one_add_ge_sub_sq {u : ℝ} (hu0 : 0 ≤ u) : u - u^2/2 ≤ Real.log (1+u) := by
  set g : ℝ → ℝ := fun t : ℝ => Real.log (1+t) - t + t^2/2 with hgdef
  have hcont : ContinuousOn g (Set.Icc 0 u) := by
    rw [hgdef]
    apply ContinuousOn.add
    · apply ContinuousOn.sub
      · apply ContinuousOn.log
        · fun_prop
        · intro t ht; have := ht.1; linarith
      · fun_prop
    · fun_prop
  have hderiv : ∀ t ∈ interior (Set.Icc 0 u),
      HasDerivWithinAt g (t^2/(1+t)) (interior (Set.Icc 0 u)) t := by
    intro t ht
    rw [interior_Icc] at ht
    have h1 : HasDerivAt (fun s : ℝ => Real.log (1+s)) (1/(1+t)) t := by
      have hin : HasDerivAt (fun s : ℝ => (1:ℝ) + s) 1 t := by
        simpa using (hasDerivAt_id t).const_add (1:ℝ)
      have h := hin.log (by linarith [ht.1])
      refine h.congr_deriv ?_
      field_simp
    have h2 : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
    have h3 : HasDerivAt (fun s : ℝ => s^2/2) t t := by
      have hp : HasDerivAt (fun s : ℝ => s^2) (2*t) t := by
        simpa using (hasDerivAt_pow 2 t)
      have h := hp.const_mul (1/2)
      have hfun : (fun s : ℝ => (1/2)*s^2) = fun s : ℝ => s^2/2 := by funext s; ring
      rw [hfun] at h
      refine h.congr_deriv ?_
      ring
    rw [hgdef]
    refine (((h1.sub h2).add h3).hasDerivWithinAt).congr_deriv ?_
    have hne : (1:ℝ) + t ≠ 0 := by linarith [ht.1]
    field_simp
    ring
  have hnonneg : ∀ t ∈ interior (Set.Icc 0 u), 0 ≤ t^2/(1+t) := by
    intro t ht
    rw [interior_Icc] at ht
    have h1t : (0:ℝ) < 1+t := by linarith [ht.1]
    exact div_nonneg (sq_nonneg t) h1t.le
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 u) hcont hderiv hnonneg
  have hmem0 : (0:ℝ) ∈ Set.Icc 0 u := ⟨le_refl 0, hu0⟩
  have hmem : u ∈ Set.Icc 0 u := ⟨hu0, le_refl u⟩
  have h := hmono hmem0 hmem hu0
  rw [hgdef] at h
  change Real.log (1+(0:ℝ)) - 0 + 0^2/2 ≤ Real.log (1+u) - u + u^2/2 at h
  have h0 : Real.log (1+(0:ℝ)) - 0 + 0^2/2 = 0 := by norm_num
  rw [h0] at h
  linarith

theorem log_one_sub_ge_neg_partial_sum (m : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) :
    -(∑ k ∈ Finset.range m, y^(k+1)/((k:ℝ)+1)) - 2*y^(m+1)/((m:ℝ)+1) ≤ Real.log (1 - y) := by
  set S : ℝ → ℝ := fun t : ℝ => ∑ k ∈ Finset.range m, t^(k+1)/((k:ℝ)+1) with hSdef
  set T : ℝ → ℝ := fun t : ℝ => 2*t^(m+1)/((m:ℝ)+1) with hTdef
  have hcont : ContinuousOn (fun t : ℝ => Real.log (1-t) + S t + T t) (Set.Icc 0 y) := by
    apply ContinuousOn.add
    · apply ContinuousOn.add
      · apply ContinuousOn.log
        · fun_prop
        · intro t ht; have := ht.2; linarith
      · rw [hSdef]; fun_prop
    · rw [hTdef]; fun_prop
  have hderiv : ∀ t ∈ interior (Set.Icc 0 y),
      HasDerivWithinAt (fun t : ℝ => Real.log (1-t) + S t + T t)
        (t^m*(1-2*t)/(1-t)) (interior (Set.Icc 0 y)) t := by
    intro t ht
    rw [interior_Icc] at ht
    have ht1 : t < 1 := by linarith [ht.2, hy1]
    have h1 : HasDerivAt (fun s : ℝ => Real.log (1-s)) (-1/(1-t)) t := by
      have hin : HasDerivAt (fun s : ℝ => (1:ℝ) - s) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub (1:ℝ)
      have h := (hin.log (by linarith))
      refine h.congr_deriv ?_
      ring
    have h3 : HasDerivAt S (∑ k ∈ Finset.range m, t^k) t := by
      rw [hSdef]
      refine HasDerivAt.fun_sum ?_
      intro k hk
      have h := (hasDerivAt_pow (k+1) t).div_const (((k:ℝ)+1))
      rw [Nat.add_sub_cancel] at h
      refine h.congr_deriv ?_
      rw [show ((k:ℝ)+1) = ((k+1:ℕ):ℝ) by push_cast; ring]
      exact mul_div_cancel_left₀ _ (by positivity)
    have h4 : HasDerivAt T (2*t^m) t := by
      rw [hTdef]
      have hp : HasDerivAt (fun s : ℝ => s^(m+1)) (((m+1:ℕ):ℝ) * t^m) t := hasDerivAt_pow (m+1) t
      have h := hp.const_mul (2/((m:ℝ)+1))
      have hfun : (fun s : ℝ => (2/((m:ℝ)+1)) * s^(m+1))
          = fun s : ℝ => 2*s^(m+1)/((m:ℝ)+1) := by funext s; ring
      rw [hfun] at h
      refine h.congr_deriv ?_
      rw [show (((m+1:ℕ):ℝ)) = ((m:ℝ)+1) by push_cast; ring]
      field_simp
    refine ((h1.add h3).add h4).hasDerivWithinAt.congr_deriv ?_
    have hne : (1:ℝ) - t ≠ 0 := by linarith
    have hgeo : (∑ k ∈ Finset.range m, t^k) * (1 - t) = 1 - t^m := geom_sum_mul_neg t m
    rw [eq_div_iff hne]
    have he1 : (1-t)*(-1/(1-t)) = -1 := by field_simp
    have hexp : (-1/(1-t) + ∑ k ∈ Finset.range m, t^k + 2*t^m) * (1-t)
        = (1-t)*(-1/(1-t)) + ((∑ k ∈ Finset.range m, t^k) * (1-t)) + 2*t^m*(1-t) := by ring
    rw [hexp, he1, hgeo]
    ring
  have hnonneg : ∀ t ∈ interior (Set.Icc 0 y), 0 ≤ t^m*(1-2*t)/(1-t) := by
    intro t ht
    rw [interior_Icc] at ht
    have h1t : 0 < 1 - t := by linarith [ht.2, hy1]
    have h2t : 0 ≤ 1 - 2*t := by linarith [ht.2, hy1]
    exact div_nonneg (mul_nonneg (pow_nonneg ht.1.le m) h2t) h1t.le
  have hmono : MonotoneOn (fun t : ℝ => Real.log (1-t) + S t + T t) (Set.Icc 0 y) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 y) hcont hderiv hnonneg
  have hmem0 : (0:ℝ) ∈ Set.Icc 0 y := ⟨le_refl 0, hy0⟩
  have hmem : y ∈ Set.Icc 0 y := ⟨hy0, le_refl y⟩
  have h := hmono hmem0 hmem hy0
  have hS0 : S 0 = 0 := by
    rw [hSdef]
    apply Finset.sum_eq_zero
    intro k hk
    rw [zero_pow (Nat.succ_ne_zero k)]
    simp
  have hT0 : T 0 = 0 := by
    rw [hTdef]
    show 2 * 0 ^ (m + 1) / ((m:ℝ) + 1) = 0
    rw [zero_pow (show m + 1 ≠ 0 by omega)]
    simp
  have hL0 : (fun t : ℝ => Real.log (1-t) + S t + T t) 0 = 0 := by
    simp only [sub_zero, Real.log_one, hS0, hT0, add_zero]
  rw [hL0] at h
  rw [hSdef, hTdef] at h
  linarith

lemma logUb_ge {b : ℝ} (h1 : (1:ℝ)/4 ≤ b) (h2 : b ≤ 1/2) : Real.log (4*b) ≤ logUb b := by
  have ha0 : (0:ℝ) ≤ 1-2*b := by linarith
  have ha1 : 1-2*b < 1 := by linarith
  have ha2 : (1:ℝ)-(1-2*b) ≠ 0 := by linarith
  have hb2 : (4:ℝ)*b = 2*(1-(1-2*b)) := by ring
  rw [logUb, hb2, Real.log_mul (by norm_num : (2:ℝ) ≠ 0) ha2]
  have h := log_one_sub_le_neg_partial_sum 8 ha0 ha1
  have h2' : Real.log 2 ≤ l2hi := log2_le_l2hi
  linarith

lemma logLb_le {b : ℝ} (h1 : (1:ℝ)/4 ≤ b) (h2 : b ≤ 1/2) : logLb b ≤ Real.log (4*b) := by
  have ha0 : (0:ℝ) ≤ 1-2*b := by linarith
  have ha1 : 1-2*b ≤ 1/2 := by linarith
  have ha2 : (1:ℝ)-(1-2*b) ≠ 0 := by linarith
  have hb2 : (4:ℝ)*b = 2*(1-(1-2*b)) := by ring
  rw [logLb, hb2, Real.log_mul (by norm_num : (2:ℝ) ≠ 0) ha2]
  have h := log_one_sub_ge_neg_partial_sum 8 ha0 ha1
  have h2' : l2lo ≤ Real.log 2 := l2lo_le_log2
  linarith

lemma rhof_bounds {b : ℝ} (h1 : (1:ℝ)/4 ≤ b) (h2 : b ≤ 1/2) : 0 ≤ rhof b ∧ rhof b ≤ 1 := by
  have hnum : (0:ℝ) ≤ 16*b^2-1 := by nlinarith [h1]
  have hden : (0:ℝ) < 64*b^2+1 := by positivity
  constructor
  · rw [rhof]; exact div_nonneg hnum hden.le
  · rw [rhof, div_le_iff₀ hden]; nlinarith [sq_nonneg b, h2]

lemma P4poly_le_lo {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1/2) : P4poly b ≤ P4r b := by
  have hu : (0:ℝ) ≤ 1-b := by linarith
  have hA : (2-b) ≠ 0 := by linarith
  have hA0 : (0:ℝ) < 2-b := by linarith
  have hb1 : 2*(2-b)^2*((2-b)^2+1/4) ≠ 0 := by positivity
  have hb2 : 2*(2-b)^2*((2-b)^2+1/16) ≠ 0 := by positivity
  have hden : (0:ℝ) < 64*(2-b)^2*((2-b)^2+1/4)*((2-b)^2+1/16) := by positivity
  have hkey : (1/2)/(2*(2-b)^2*((2-b)^2+1/4)) - (1/4)/(2*(2-b)^2*((2-b)^2+1/16))
      = (8*(2-b)^2 - 1)/(64*(2-b)^2*((2-b)^2+1/4)*((2-b)^2+1/16)) := by
    rw [div_sub_div _ _ hb1 hb2]
    field_simp
    ring
  rw [P4r, hkey, show (((2-b)^2-b^2)^2/8) = 2*(1-b)^2 by ring, ← mul_div_assoc]
  rw [le_div_iff₀ hden]
  have hcert : (0:ℝ) ≤ 2*(1-b)^2*(8*(2-b)^2-1)
      - P4poly b * (64*(2-b)^2*((2-b)^2+1/4)*((2-b)^2+1/16)) := by
    have hh : 2*(1-b)^2*(8*(2-b)^2-1)
        - P4poly b * (64*(2-b)^2*((2-b)^2+1/4)*((2-b)^2+1/16)) = ((2747987647/156250000))*(1/2-b)^11 + ((52524354091/312500000))*(1/2-b)^10 + ((1725221250287/2500000000))*(1/2-b)^9 + ((7907134870329/5000000000))*(1/2-b)^8 + ((4405163829339/2000000000))*(1/2-b)^7 + ((38243094634279/20000000000))*(1/2-b)^6 + ((41222488130821/40000000000))*(1/2-b)^5 + ((26943899794481/80000000000))*(1/2-b)^4 + ((10179672924777)/160000000000)*(1/2-b)^3 + ((2121031596857/320000000000))*(1/2-b)^2 + ((11291551691/20000000000))*(1/2-b)^1 + (11180853377/128000000000) := by
      simp only [P4poly]; ring
    rw [hh]; positivity
  linarith

lemma P5poly_le_lo {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1/2) : P5poly b ≤ P5r b := by
  have hA0 : (0:ℝ) < 2-b := by linarith
  have hA1 : (2-b)^2+1/4 ≠ 0 := by positivity
  have hA2 : (2-b)^2+1/16 ≠ 0 := by positivity
  have hD : (2-b)^4*(4*(2-b)^2+1)^2*(16*(2-b)^2+1)^2 ≠ 0 := by positivity
  have hden : (0:ℝ) < (2-b)^4*(4*(2-b)^2+1)^2*(16*(2-b)^2+1)^2 := by positivity
  have hid : P5r b = ((-2560)*b^9 + (38400)*b^8 + (-253472)*b^7 + (965472)*b^6 + (-2336260)*b^5
        + (3720604)*b^4 + (-3895593)*b^3 + (2583547)*b^2 + (-984119)*b + 163981)
      /((2-b)^4*(4*(2-b)^2+1)^2*(16*(2-b)^2+1)^2) := by
    rw [P5r]; field_simp; ring
  rw [hid, le_div_iff₀ hden]
  have hcert : (0:ℝ) ≤ ((-2560)*b^9 + (38400)*b^8 + (-253472)*b^7 + (965472)*b^6 + (-2336260)*b^5
        + (3720604)*b^4 + (-3895593)*b^3 + (2583547)*b^2 + (-984119)*b + 163981)
      - P5poly b * ((2-b)^4*(4*(2-b)^2+1)^2*(16*(2-b)^2+1)^2) := by
    have hh : ((-2560)*b^9 + (38400)*b^8 + (-253472)*b^7 + (965472)*b^6 + (-2336260)*b^5
        + (3720604)*b^4 + (-3895593)*b^3 + (2583547)*b^2 + (-984119)*b + 163981)
        - P5poly b * ((2-b)^4*(4*(2-b)^2+1)^2*(16*(2-b)^2+1)^2) = (3859595565816832/390625)*(1/2-b)^16 + (201166240995889664/1953125)*(b-0)^1*(1/2-b)^15 + (4866889613019439232/9765625)*(b-0)^2*(1/2-b)^14 + (116010254067922048/78125)*(b-0)^3*(1/2-b)^13 + (29762601654730117724/9765625)*(b-0)^4*(1/2-b)^12 + (44594589709339589926/9765625)*(b-0)^5*(1/2-b)^11 + (50444209913963123436/9765625)*(b-0)^6*(1/2-b)^10 + (43946136592497828741/9765625)*(b-0)^7*(1/2-b)^9 + (29821490235175102101/9765625)*(b-0)^8*(1/2-b)^8 + (15846087917143689244/9765625)*(b-0)^9*(1/2-b)^7 + (6596719391075656646/9765625)*(b-0)^10*(1/2-b)^6 + (2143317825755037009/9765625)*(b-0)^11*(1/2-b)^5 + (107692602892524861/1953125)*(b-0)^12*(1/2-b)^4 + (20517918385064396/1953125)*(b-0)^13*(1/2-b)^3 + (14205974610236216/9765625)*(b-0)^14*(1/2-b)^2 + (258729713464044/1953125)*(b-0)^15*(1/2-b)^1 + (2342495287524/390625)*(b-0)^16 := by
      simp only [P5poly]; ring
    rw [hh]; positivity
  linarith

theorem integral_T_term_ge {β : ℝ} (hβ0 : 0 < β) (hβ2 : β ≤ 1/2) :
    (13/5)*(psi7 (dl1 β) + psi7 (dl2 β)) + Ctot β * psi7 (dlr β) + P4poly β + P5poly β
      ≤ ∫ s in (1/4:ℝ)..(1/2), Tterm β s := by
  have hβ1 : β < 1 := by linarith
  rw [integral_T_term hβ0 hβ1]
  have h1 : psi7 (dl1 β) ≤ FA β := by
    rw [FA_eq_arctan hβ0 hβ1]
    obtain ⟨ha, hb⟩ := dl1_bound hβ1
    exact psi7_le_arctan ha.le hb
  have h2 : psi7 (dl2 β) ≤ FB β := by
    rw [FB_eq_arctan hβ0 hβ1]
    obtain ⟨ha, hb⟩ := dl2_bound hβ0
    exact psi7_le_arctan ha.le hb
  have h3 : psi7 (dlr β) ≤ FD β := by
    rw [FD_eq_arctan hβ0 hβ1]
    obtain ⟨ha, hb⟩ := dlr_bound hβ1
    exact psi7_le_arctan ha.le hb
  have hCt0 : 0 ≤ Ctot β := by
    rw [Ctot]
    have hA : (0:ℝ) < 2-β := by linarith
    have he : (2-β)^2-β^2 = 4*(1-β) := by ring
    rw [he]
    positivity
  have hP4 : P4poly β ≤ P4r β := P4poly_le_lo hβ0.le hβ2
  have hP5 : P5poly β ≤ P5r β := P5poly_le_lo hβ0.le hβ2
  have h5 : (13/5)*psi7 (dl1 β) + (13/5)*psi7 (dl2 β) ≤ (13/5)*(FA β + FB β) := by
    have h1' := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 13/5)
    have h2' := mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 13/5)
    linarith
  have h6 := mul_le_mul_of_nonneg_left h3 hCt0
  linarith

/-! ## I. The three elementary integrals over `[1/4,β]` -/

lemma integral_one_sub_v_Icc {β : ℝ} (hβ4 : (1:ℝ)/4 ≤ β) :
    (∫ s in (1/4:ℝ)..β, (1 - s^2/(2*((2-β)^2+β^2))))
      = (β-1/4) - (β^3-1/64)/(6*((2-β)^2+β^2)) := by
  have hS : (0:ℝ) < (2-β)^2+β^2 := by nlinarith [sq_nonneg (2-β), sq_nonneg β, hβ4]
  have hcont : ContinuousOn (fun s : ℝ => 1 - s^2/(2*((2-β)^2+β^2))) (Set.uIcc (1/4:ℝ) β) := by
    apply ContinuousOn.sub continuousOn_const
    exact (Continuous.continuousOn (by fun_prop)).div_const _
  have hderiv : ∀ s ∈ Set.uIcc (1/4:ℝ) β,
      HasDerivAt (fun s : ℝ => s - s^3/(6*((2-β)^2+β^2))) (1 - s^2/(2*((2-β)^2+β^2))) s := by
    intro s hs
    have hp : HasDerivAt (fun s : ℝ => s^3) (3*s^2) s := by
      simpa using (hasDerivAt_pow 3 s)
    have h1 : HasDerivAt (fun s : ℝ => s^3/(6*((2-β)^2+β^2))) (3*s^2/(6*((2-β)^2+β^2))) s :=
      hp.div_const _
    have h := (hasDerivAt_id s).sub h1
    refine h.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  ring_nf

lemma integral_z_Icc {β : ℝ} (hβ0 : 0 < β) (hβ4 : (1:ℝ)/4 ≤ β) :
    (∫ s in (1/4:ℝ)..β, (2*β-s)^2/(4*β*s))
      = β*Real.log (4*β) - 7*β/8 + 1/4 - 1/(128*β) := by
  have hβne : β ≠ 0 := ne_of_gt hβ0
  have hcont : ContinuousOn (fun s : ℝ => (2*β-s)^2/(4*β*s)) (Set.uIcc (1/4:ℝ) β) := by
    intro s hs
    rw [Set.uIcc_of_le hβ4] at hs
    have hs0 : (0:ℝ) < s := by linarith [hs.1]
    apply ContinuousAt.continuousWithinAt
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)
  have hderiv : ∀ s ∈ Set.uIcc (1/4:ℝ) β,
      HasDerivAt (fun s : ℝ => (1/(4*β))*(4*β^2*Real.log s - 4*β*s + s^2/2))
        ((2*β-s)^2/(4*β*s)) s := by
    intro s hs
    rw [Set.uIcc_of_le hβ4] at hs
    have hs0 : (0:ℝ) < s := by linarith [hs.1]
    have ha : HasDerivAt (fun s : ℝ => Real.log s) (1/s) s := by
      simpa [one_div] using Real.hasDerivAt_log (ne_of_gt hs0)
    have hb : HasDerivAt (fun s : ℝ => 4*β^2*Real.log s) (4*β^2*(1/s)) s := ha.const_mul _
    have hc : HasDerivAt (fun s : ℝ => 4*β*s) (4*β) s := by
      simpa using (hasDerivAt_id s).const_mul (4*β)
    have hd : HasDerivAt (fun s : ℝ => s^2/2) s s := by
      have hp : HasDerivAt (fun s : ℝ => s^2) (2*s) s := by
        simpa using (hasDerivAt_pow 2 s)
      have h := hp.const_mul (1/2)
      have hfun : (fun s : ℝ => (1/2)*s^2) = fun s : ℝ => s^2/2 := by funext s; ring
      rw [hfun] at h
      refine h.congr_deriv ?_
      ring
    have h := ((hb.sub hc).add hd).const_mul (1/(4*β))
    refine h.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  have hlog2 : Real.log β - Real.log ((1:ℝ)/4) = Real.log (4*β) := by
    rw [← Real.log_div hβne (by norm_num : ((1:ℝ)/4) ≠ 0)]
    congr 1
    ring
  have hmain : (1/(4*β))*(4*β^2*Real.log β - 4*β*β + β^2/2)
      - (1/(4*β))*(4*β^2*Real.log ((1:ℝ)/4) - 4*β*((1:ℝ)/4) + ((1:ℝ)/4)^2/2)
      = β*(Real.log β - Real.log ((1:ℝ)/4)) - 7*β/8 + 1/4 - 1/(128*β) := by
    field_simp
    ring
  rw [hmain, hlog2]

lemma integral_zdiv_Icc {β : ℝ} (hβ0 : 0 < β) (hβ4 : (1:ℝ)/4 ≤ β) :
    (∫ s in (1/4:ℝ)..β, (2*β-s)^2/(4*β^2+s^2))
      = (β-1/4) - 2*β*Real.log (5*β^2/(4*β^2+1/16)) := by
  have hpos : ∀ s ∈ Set.uIcc (1/4:ℝ) β, (0:ℝ) < 4*β^2+s^2 := by
    intro s hs; positivity
  have hcont : ContinuousOn (fun s : ℝ => (2*β-s)^2/(4*β^2+s^2)) (Set.uIcc (1/4:ℝ) β) := by
    intro s hs
    apply ContinuousAt.continuousWithinAt
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)
  have hderiv : ∀ s ∈ Set.uIcc (1/4:ℝ) β,
      HasDerivAt (fun s : ℝ => s - 2*β*Real.log (4*β^2+s^2)) ((2*β-s)^2/(4*β^2+s^2)) s := by
    intro s hs
    have hp : HasDerivAt (fun s : ℝ => s^2) (2*s) s := by
      simpa using (hasDerivAt_pow 2 s)
    have h1 : HasDerivAt (fun s : ℝ => 4*β^2+s^2) (2*s) s := by
      have h := (hasDerivAt_const (x := s) (c := 4*β^2)).add hp
      have hfun : ((fun _ : ℝ => 4*β^2) + fun s : ℝ => s^2) = fun s : ℝ => 4*β^2 + s^2 := by
        funext x; simp only [Pi.add_apply]
      rw [hfun] at h
      exact h.congr_deriv (by ring)
    have h2 : HasDerivAt (fun s : ℝ => Real.log (4*β^2+s^2)) (2*s/(4*β^2+s^2)) s := by
      have h := h1.log (ne_of_gt (hpos s hs))
      refine h.congr_deriv ?_
      ring
    have h3 : HasDerivAt (fun s : ℝ => 2*β*Real.log (4*β^2+s^2))
        (2*β*(2*s/(4*β^2+s^2))) s := h2.const_mul (2*β)
    have h := (hasDerivAt_id s).sub h3
    refine h.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  have hlog : Real.log (4*β^2+β^2) - Real.log (4*β^2+(1/4)^2)
      = Real.log (5*β^2/(4*β^2+1/16)) := by
    rw [← Real.log_div (by positivity : (4*β^2+β^2) ≠ 0) (by positivity : (4*β^2+((1:ℝ)/4)^2) ≠ 0)]
    congr 1
    ring
  have hmain : (β - 2*β*Real.log (4*β^2+β^2)) - ((1:ℝ)/4 - 2*β*Real.log (4*β^2+(1/4)^2))
      = (β-1/4) - 2*β*(Real.log (4*β^2+β^2) - Real.log (4*β^2+(1/4)^2)) := by
    ring
  rw [hmain, hlog]

/-! ## J. `∫_{1/4}^β Lterm ≤ Lb β` -/

lemma half_div_add_half_div_one_add (Z : ℝ) :
    Z/2 + Z/(2*(1+Z)) = (1/2)*Z + (1/2)*(Z/(1+Z)) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
  ring

lemma integral_Lterm_le_Lb {β : ℝ} (hβ4 : (1:ℝ)/4 ≤ β) (hβ2 : β ≤ 1/2) :
    (∫ s in (1/4:ℝ)..β, Lterm β s) ≤ Lb β := by
  have hβ0 : 0 < β := by linarith
  have hS : (0:ℝ) < (2-β)^2+β^2 := by nlinarith [sq_nonneg (2-β), sq_nonneg β, hβ4]
  have hSb : Sb β = (2-β)^2+β^2 := by rw [Sb]; ring
  have hpt : ∀ s ∈ Set.Icc (1/4:ℝ) β,
      Lterm β s ≤ l2hi*(1 - s^2/(2*((2-β)^2+β^2)))
        + (1/2)*((2*β-s)^2/(4*β*s))
        + (1/2)*(((2*β-s)^2/(4*β*s))/(1+(2*β-s)^2/(4*β*s))) := by
    intro s hs
    have hs0 : (0:ℝ) < s := by linarith [hs.1]
    have hsβ : s ≤ β := hs.2
    have hzv : (0:ℝ) ≤ (2*β-s)^2/(4*β*s) := by positivity
    have hlz : (0:ℝ) ≤ Real.log (1+(2*β-s)^2/(4*β*s)) := Real.log_nonneg (by linarith)
    have hv0 : (0:ℝ) ≤ s^2/(2*((2-β)^2+β^2)) := by positivity
    have hv1 : s^2/(2*((2-β)^2+β^2)) ≤ 1 := by
      rw [div_le_one (by positivity : (0:ℝ) < 2*((2-β)^2+β^2))]
      nlinarith [mul_self_le_mul_self hs0.le hsβ, sq_nonneg (2-β), sq_nonneg β]
    have hlogeq : (4*β^2+s^2)/(2*β*s) = 2*(1+(2*β-s)^2/(4*β*s)) := by
      field_simp
      ring
    rw [Lterm, hlogeq,
      Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity : (1:ℝ)+(2*β-s)^2/(4*β*s) ≠ 0)]
    have h1 : Real.log 2*(1 - s^2/(2*((2-β)^2+β^2)))
        ≤ l2hi*(1 - s^2/(2*((2-β)^2+β^2))) :=
      mul_le_mul_of_nonneg_right log2_le_l2hi (by linarith)
    have h2 : Real.log (1+(2*β-s)^2/(4*β*s))*(1 - s^2/(2*((2-β)^2+β^2)))
        ≤ Real.log (1+(2*β-s)^2/(4*β*s)) := by
      nlinarith [mul_le_mul_of_nonneg_left hv1 hlz]
    have h3 : Real.log (1+(2*β-s)^2/(4*β*s))
        ≤ (1/2)*((2*β-s)^2/(4*β*s))
          + (1/2)*(((2*β-s)^2/(4*β*s))/(1+(2*β-s)^2/(4*β*s))) := by
      have h := Commons.Analysis.Real.log_one_add_le_half_add hzv
      have he := half_div_add_half_div_one_add ((2*β-s)^2/(4*β*s))
      linarith [h, he.ge]
    have hdist : (Real.log 2 + Real.log (1+(2*β-s)^2/(4*β*s)))*(1 - s^2/(2*((2-β)^2+β^2)))
        = Real.log 2*(1 - s^2/(2*((2-β)^2+β^2)))
          + Real.log (1+(2*β-s)^2/(4*β*s))*(1 - s^2/(2*((2-β)^2+β^2))) := by ring
    rw [hdist]
    linarith [h1, h2, h3]
  have hA : IntervalIntegrable (fun s : ℝ => 1 - s^2/(2*((2-β)^2+β^2))) volume (1/4) β :=
    (by fun_prop : Continuous fun s : ℝ => 1 - s^2/(2*((2-β)^2+β^2))).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun s : ℝ => (2*β-s)^2/(4*β*s)) volume (1/4) β := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    rw [Set.uIcc_of_le hβ4] at hs
    have hs0 : (0:ℝ) < s := by linarith [hs.1]
    apply ContinuousAt.continuousWithinAt
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)
  have hC : IntervalIntegrable (fun s : ℝ => ((2*β-s)^2/(4*β*s))/(1+(2*β-s)^2/(4*β*s)))
      volume (1/4) β := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    rw [Set.uIcc_of_le hβ4] at hs
    have hs0 : (0:ℝ) < s := by linarith [hs.1]
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.div _ _ (by positivity)
    · exact ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)
    · exact continuousAt_const.add (ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity))
  have hcontL : IntervalIntegrable (fun s : ℝ => Lterm β s) volume (1/4) β := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    rw [Set.uIcc_of_le hβ4] at hs
    have hs0 : (0:ℝ) < s := by linarith [hs.1]
    apply ContinuousAt.continuousWithinAt
    simp only [Lterm]
    apply ContinuousAt.mul
    · apply ContinuousAt.log
      · exact ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)
      · positivity
    · fun_prop
  have hR : IntervalIntegrable (fun s : ℝ => l2hi*(1 - s^2/(2*((2-β)^2+β^2)))
        + (1/2)*((2*β-s)^2/(4*β*s))
        + (1/2)*(((2*β-s)^2/(4*β*s))/(1+(2*β-s)^2/(4*β*s)))) volume (1/4) β :=
    ((hA.const_mul l2hi).add (hB.const_mul (1/2))).add (hC.const_mul (1/2))
  have hmono := intervalIntegral.integral_mono_on hβ4 hcontL hR hpt
  have hid : ∀ s ∈ Set.uIcc (1/4:ℝ) β,
      ((2*β-s)^2/(4*β*s))/(1+(2*β-s)^2/(4*β*s)) = (2*β-s)^2/(4*β^2+s^2) := by
    intro s hs
    rw [Set.uIcc_of_le hβ4] at hs
    have hs0 : (0:ℝ) < s := by linarith [hs.1]
    field_simp
    ring
  have hidI : (∫ s in (1/4:ℝ)..β, ((2*β-s)^2/(4*β*s))/(1+(2*β-s)^2/(4*β*s)))
      = ∫ s in (1/4:ℝ)..β, (2*β-s)^2/(4*β^2+s^2) :=
    intervalIntegral.integral_congr hid
  have hInt : (∫ s in (1/4:ℝ)..β, (l2hi*(1 - s^2/(2*((2-β)^2+β^2)))
        + (1/2)*((2*β-s)^2/(4*β*s))
        + (1/2)*(((2*β-s)^2/(4*β*s))/(1+(2*β-s)^2/(4*β*s)))))
      = l2hi*(∫ s in (1/4:ℝ)..β, (1 - s^2/(2*((2-β)^2+β^2))))
        + (1/2)*(∫ s in (1/4:ℝ)..β, (2*β-s)^2/(4*β*s))
        + (1/2)*(∫ s in (1/4:ℝ)..β, ((2*β-s)^2/(4*β*s))/(1+(2*β-s)^2/(4*β*s))) := by
    rw [intervalIntegral.integral_add ((hA.const_mul l2hi).add (hB.const_mul (1/2))) (hC.const_mul (1/2)),
      intervalIntegral.integral_add (hA.const_mul l2hi) (hB.const_mul (1/2)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [hInt] at hmono
  rw [integral_one_sub_v_Icc hβ4, integral_z_Icc hβ0 hβ4, hidI, integral_zdiv_Icc hβ0 hβ4] at hmono
  have hP1 : l2hi * ((β-1/4) - (β^3-1/64)/(6*((2-β)^2+β^2))) = P1f β := by
    rw [P1f, hSb]
  rw [hP1] at hmono
  have hP2 : (1/2)*(β*Real.log (4*β) - 7*β/8 + 1/4 - 1/(128*β)) ≤ P2f β := by
    rw [P2f]
    have h1 : β*Real.log (4*β) ≤ β*logUb β :=
      mul_le_mul_of_nonneg_left (logUb_ge hβ4 hβ2) hβ0.le
    linarith
  have hrho := rhof_bounds hβ4 hβ2
  have h5b : 5*β^2/(4*β^2+1/16) = 1 + rhof β := by
    rw [rhof]; field_simp; ring
  have hlogrho : rhof β - (rhof β)^2/2 ≤ Real.log (5*β^2/(4*β^2+1/16)) := by
    rw [h5b]
    exact log_one_add_ge_sub_sq hrho.1
  have hP3 : (1/2)*((β-1/4) - 2*β*Real.log (5*β^2/(4*β^2+1/16))) ≤ P3f β := by
    rw [P3f]
    have h2 : 2*β*(rhof β - (rhof β)^2/2) ≤ 2*β*Real.log (5*β^2/(4*β^2+1/16)) :=
      mul_le_mul_of_nonneg_left hlogrho (by linarith)
    linarith
  rw [Lb]
  linarith [hmono, hP2, hP3]

/-! ## K. `∫_β^{1/2} Eterm ≤ Eb β` -/

lemma integral_Eterm_le_Eb {β : ℝ} (hβ4 : (1:ℝ)/4 ≤ β) (hβ2 : β ≤ 1/2) :
    (∫ s in β..(1/2), Eterm β s) ≤ Eb β := by
  have hβ0 : 0 < β := by linarith
  have hA : (0:ℝ) < 2-β := by linarith
  rw [integral_E_half hβ0 hβ2 hβ4]
  have hy1 : (1:ℝ) ≤ (2-β)/β := by
    rw [le_div_iff₀ hβ0]; linarith
  have hy2 : (1:ℝ) ≤ 2*(2-β) := by linarith
  obtain ⟨hl1, hu1⟩ := Commons.Analysis.Real.arsinh_log_bounds hy1
  obtain ⟨hl2, hu2⟩ := Commons.Analysis.Real.arsinh_log_bounds hy2
  have hsum : Real.arsinh ((2-β)/β) - Real.arsinh (2*(2-β))
      ≤ Real.log (2*((2-β)/β)) + 1/(4*((2-β)/β)^2)
        - Real.log (2*(2*(2-β))) - 1/(4*(2*(2-β))^2) + 3/(32*(2*(2-β))^4) := by
    linarith
  have hkey2 : Real.log (2*((2-β)/β)) - Real.log (2*(2*(2-β))) = -Real.log (2*β) := by
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity : ((2-β)/β) ≠ 0),
        Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity : (2*(2-β)) ≠ 0),
        Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity : (2-β) ≠ 0),
        Real.log_div (by positivity : (2-β) ≠ 0) (ne_of_gt hβ0)]
    have h4 : Real.log (2*β) = Real.log 2 + Real.log β :=
      Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hβ0)
    rw [h4]
    ring
  have hrat : 1/(4*((2-β)/β)^2) - 1/(4*(2*(2-β))^2) + 3/(32*(2*(2-β))^4)
      = (4*β^2-1)/(16*(2-β)^2) + 3/(512*(2-β)^4) := by
    field_simp
    ring
  have hval : Real.log (2*((2-β)/β)) + 1/(4*((2-β)/β)^2)
        - Real.log (2*(2*(2-β))) - 1/(4*(2*(2-β))^2) + 3/(32*(2*(2-β))^4)
      = -Real.log (2*β) + (4*β^2-1)/(16*(2-β)^2) + 3/(512*(2-β)^4) := by
    have h5 : Real.log (2*((2-β)/β)) = Real.log (2*(2*(2-β))) - Real.log (2*β) := by
      linarith [hkey2]
    rw [h5]
    linarith [hrat]
  have hlogL : -β*Real.log (2*β) ≤ -β*logLb β + β*l2hi := by
    have h1 : logLb β ≤ Real.log (4*β) := logLb_le hβ4 hβ2
    have h2 : Real.log (2*β) = Real.log (4*β) - Real.log 2 := by
      rw [show (4:ℝ)*β = 2*(2*β) by ring,
        Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity : (2*β) ≠ 0)]
      ring
    have h3 : Real.log 2 ≤ l2hi := log2_le_l2hi
    have e1 : -β*Real.log (4*β) ≤ -β*logLb β := by
      have := mul_le_mul_of_nonneg_left h1 hβ0.le
      linarith
    have e2 : β*Real.log 2 ≤ β*l2hi := mul_le_mul_of_nonneg_left h3 hβ0.le
    have he : -β*Real.log (2*β) = -β*Real.log (4*β) + β*Real.log 2 := by
      rw [h2]; ring
    linarith [he.le, e1, e2]
  have h1' : β*(Real.arsinh ((2-β)/β) - Real.arsinh (2*(2-β)))
      ≤ -β*Real.log (2*β) + β*(4*β^2-1)/(16*(2-β)^2) + 3*β/(512*(2-β)^4) := by
    have hh := mul_le_mul_of_nonneg_left (hsum.trans_eq hval) hβ0.le
    have he : β*(-Real.log (2*β) + (4*β^2-1)/(16*(2-β)^2) + 3/(512*(2-β)^4))
        = -β*Real.log (2*β) + β*(4*β^2-1)/(16*(2-β)^2) + 3*β/(512*(2-β)^4) := by ring
    linarith [hh, he.le]
  rw [Eb, E1f, E3f, E4f]
  linarith [h1', hlogL]

/-! ## L. Integrability and the two bridges -/

lemma intervalIntegrable_Tterm {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    IntervalIntegrable (fun s : ℝ => Tterm β s) volume (1/4) (1/2) := by
  have hA : (0:ℝ) < 2-β := by linarith
  have h1 : (0:ℝ) < 3/2-β := by linarith
  have h2 : (0:ℝ) < 1+β := by linarith
  have hcA : Continuous fun s : ℝ => ((3/2-β) : ℝ)/((3/2-β)^2+s^2) :=
    (continuous_const (y := ((3/2-β):ℝ))).div (by fun_prop) (by intro s; positivity)
  have hcB : Continuous fun s : ℝ => ((1+β) : ℝ)/((1+β)^2+s^2) :=
    (continuous_const (y := ((1+β):ℝ))).div (by fun_prop) (by intro s; positivity)
  have hcAB : Continuous fun s : ℝ => (13/5)*(((3/2-β)/((3/2-β)^2+s^2))+((1+β)/((1+β)^2+s^2))) :=
    Continuous.const_mul (hcA.add hcB) _
  have hc1 : Continuous fun s : ℝ => (((2-β)^2-β^2) : ℝ)/(2*((2-β)^2+s^2)) :=
    (continuous_const (y := ((2-β)^2-β^2 : ℝ))).div (by fun_prop) (by intro s; positivity)
  have hc2 : Continuous fun s : ℝ => (((2-β)^2-β^2)^2 : ℝ)/(8*((2-β)^2+s^2)^2) :=
    (continuous_const (y := (((2-β)^2-β^2)^2 : ℝ))).div (by fun_prop) (by intro s; positivity)
  have hc3 : Continuous fun s : ℝ => (((2-β)^2-β^2)^3 : ℝ)/(16*((2-β)^2+s^2)^3) :=
    (continuous_const (y := (((2-β)^2-β^2)^3 : ℝ))).div (by fun_prop) (by intro s; positivity)
  have hc : Continuous (fun s : ℝ => Tterm β s) := by
    unfold Tterm
    exact ((hcAB.add hc1).add hc2).add hc3
  exact hc.intervalIntegrable _ _

lemma intervalIntegrable_N1term {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    IntervalIntegrable (fun s : ℝ => N1term β s) volume (1/4) (1/2) := by
  apply ContinuousOn.intervalIntegrable
  intro s hs
  rw [Set.uIcc_of_le (by norm_num : (1:ℝ)/4 ≤ 1/2)] at hs
  have hs0 : (0:ℝ) < s := by linarith [hs.1]
  have hAb : (0:ℝ) < 2-β := by linarith
  have hN1 : N1term β = fun s : ℝ =>
      Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s))*(1 - s^2/(4*(2-β)^2)) := rfl
  rw [hN1]
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.mul
  · apply ContinuousAt.log
    · apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · exact ne_of_gt (by positivity : (0:ℝ) < 2*(2-β)*s)
    · positivity
  · fun_prop

lemma intervalIntegrable_Eterm {β : ℝ} (hβ0 : 0 < β) (hβ2 : β ≤ 1/2) :
    IntervalIntegrable (fun s : ℝ => Eterm β s) volume (1/4) (1/2) := by
  apply ContinuousOn.intervalIntegrable
  intro s hs
  rw [Set.uIcc_of_le (by norm_num : (1:ℝ)/4 ≤ 1/2)] at hs
  have hs0 : (0:ℝ) < s := by linarith [hs.1]
  apply ContinuousAt.continuousWithinAt
  simp only [Eterm]
  exact ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)

lemma intervalIntegrable_Lterm {β : ℝ} (hβ0 : 0 < β) (hβ4 : (1:ℝ)/4 ≤ β) :
    IntervalIntegrable (fun s : ℝ => Lterm β s) volume (1/4) β := by
  apply ContinuousOn.intervalIntegrable
  intro s hs
  rw [Set.uIcc_of_le hβ4] at hs
  have hs0 : (0:ℝ) < s := by linarith [hs.1]
  apply ContinuousAt.continuousWithinAt
  simp only [Lterm]
  apply ContinuousAt.mul
  · apply ContinuousAt.log
    · exact ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)
    · positivity
  · fun_prop

theorem G1_le_integral {β : ℝ} (hβ0 : 0 < β) (hβ4 : β ≤ 1/4) :
    G1 β ≤ ∫ s in (1/4:ℝ)..(1/2),
      (Tterm β s - N1term β s - (if s ≤ β then Lterm β s else Eterm β s)) := by
  have hβ1 : β < 1 := by linarith
  have hβ12 : β ≤ 1/2 := by linarith
  have hcT := intervalIntegrable_Tterm hβ0 hβ1
  have hcN1 := intervalIntegrable_N1term hβ0 hβ1
  have hcE := intervalIntegrable_Eterm hβ0 hβ12
  have hae : (∫ s in (1/4:ℝ)..(1/2),
        (Tterm β s - N1term β s - (if s ≤ β then Lterm β s else Eterm β s)))
      = ∫ s in (1/4:ℝ)..(1/2), (Tterm β s - N1term β s - Eterm β s) := by
    apply intervalIntegral.integral_congr_ae
    exact Filter.Eventually.of_forall (fun s hs => by
      rw [Set.uIoc_of_le (by norm_num : (1:ℝ)/4 ≤ 1/2)] at hs
      have : ¬ (s ≤ β) := by linarith [hs.1]
      simp only [this, if_false])
  rw [hae]
  have hlin : (∫ s in (1/4:ℝ)..(1/2), (Tterm β s - N1term β s - Eterm β s))
      = (∫ s in (1/4:ℝ)..(1/2), Tterm β s) - (∫ s in (1/4:ℝ)..(1/2), N1term β s)
        - ∫ s in (1/4:ℝ)..(1/2), Eterm β s := by
    rw [intervalIntegral.integral_sub (hcT.sub hcN1) hcE, intervalIntegral.integral_sub hcT hcN1]
  rw [hlin]
  have hT : (13/5)*(psi7 (dl1 β) + psi7 (dl2 β)) + Ctot β * psi7 (dlr β) + P4poly β + P5poly β
      ≤ ∫ s in (1/4:ℝ)..(1/2), Tterm β s := integral_T_term_ge hβ0 hβ12
  have hN : (∫ s in (1/4:ℝ)..(1/2), N1term β s) ≤ Real.log (2*(2-β)) * I0f β + stuff1f β :=
    integral_N1_le hβ0 hβ1
  have hI0 : 0 ≤ I0f β := by
    rw [I0f]
    have hh : 7/(768*(2-β)^2) ≤ 7/768 := by
      apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 7) (by norm_num : (0:ℝ) < 768)
      nlinarith [sq_nonneg (2-β), hβ1]
    linarith
  have hmul : Real.log (2*(2-β)) * I0f β ≤ LAf β * I0f β :=
    mul_le_mul_of_nonneg_right (log_2A_le_LAf hβ0 hβ1) hI0
  have hE1 : (∫ s in (1/4:ℝ)..(1/2), Eterm β s)
      = β*(Real.arsinh (4*(2-β)) - Real.arsinh (2*(2-β))) := integral_E_Icc hβ0 hβ12
  have hE2 : β*(Real.arsinh (4*(2-β)) - Real.arsinh (2*(2-β))) ≤ β*l2hi := by
    have hy1 : (1:ℝ) ≤ 4*(2-β) := by linarith
    have hy2 : (1:ℝ) ≤ 2*(2-β) := by linarith
    obtain ⟨hl1, hu1⟩ := Commons.Analysis.Real.arsinh_log_bounds hy1
    obtain ⟨hl2, hu2⟩ := Commons.Analysis.Real.arsinh_log_bounds hy2
    have hsum : Real.arsinh (4*(2-β)) - Real.arsinh (2*(2-β))
        ≤ Real.log (2*(4*(2-β))) + 1/(4*(4*(2-β))^2)
          - Real.log (2*(2*(2-β))) - 1/(4*(2*(2-β))^2) + 3/(32*(2*(2-β))^4) := by
      linarith
    have hval : Real.log (2*(4*(2-β))) + 1/(4*(4*(2-β))^2)
          - Real.log (2*(2*(2-β))) - 1/(4*(2*(2-β))^2) + 3/(32*(2*(2-β))^4)
        = Real.log 2 - 3/(64*(2-β)^2) + 3/(512*(2-β)^4) := by
      have hlog2 : Real.log (2*(4*(2-β))) - Real.log (2*(2*(2-β))) = Real.log 2 := by
        rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity : (4*(2-β)) ≠ 0),
            Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity : (2*(2-β)) ≠ 0)]
        have h5 : Real.log ((4:ℝ)*(2-β)) = Real.log 2 + Real.log (2*(2-β)) := by
          rw [show (4:ℝ)*(2-β) = 2*(2*(2-β)) by ring]
          exact Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity : (2*(2-β)) ≠ 0)
        rw [h5]
        ring
      have hrat : 1/(4*(4*(2-β))^2) - 1/(4*(2*(2-β))^2) + 3/(32*(2*(2-β))^4)
          = -3/(64*(2-β)^2) + 3/(512*(2-β)^4) := by
        field_simp
        ring
      have hLHS : Real.log (2*(4*(2-β))) + 1/(4*(4*(2-β))^2)
            - Real.log (2*(2*(2-β))) - 1/(4*(2*(2-β))^2) + 3/(32*(2*(2-β))^4)
          = (Real.log (2*(4*(2-β))) - Real.log (2*(2*(2-β))))
            + (1/(4*(4*(2-β))^2) - 1/(4*(2*(2-β))^2) + 3/(32*(2*(2-β))^4)) := by ring
      rw [hLHS, hlog2, hrat]
      ring
    have hle : Real.log 2 - 3/(64*(2-β)^2) + 3/(512*(2-β)^4) ≤ l2hi := by
      have hA2 : (0:ℝ) < 64*(2-β)^2 := by
        have h : (0:ℝ) < 2-β := by linarith
        positivity
      have h1 : 3/(512*(2-β)^4) ≤ 3/(64*(2-β)^2) := by
        apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 3) hA2
        have hAp : (0:ℝ) ≤ (2-β)^2 := sq_nonneg _
        have hA4 : (1:ℝ)/8 ≤ (2-β)^2 := by nlinarith [sq_nonneg (2-β-7/4)]
        nlinarith [mul_nonneg hAp (by linarith : (0:ℝ) ≤ 8*(2-β)^2 - 1)]
      have h2 : Real.log 2 ≤ l2hi := log2_le_l2hi
      linarith
    have h3 := hsum.trans hval.le
    have h4 := h3.trans hle
    nlinarith [h4, hβ0.le]
  rw [hE1]
  rw [G1]
  linarith [hT, hN, hmul, hE2]

theorem Gh_le_integral {β : ℝ} (hβ4 : (1:ℝ)/4 ≤ β) (hβ2 : β ≤ 1/2) :
    Gh β ≤ ∫ s in (1/4:ℝ)..(1/2),
      (Tterm β s - N1term β s - (if s ≤ β then Lterm β s else Eterm β s)) := by
  have hβ0 : 0 < β := by linarith
  have hβ1 : β < 1 := by linarith
  have hcT := intervalIntegrable_Tterm hβ0 hβ1
  have hcN1 := intervalIntegrable_N1term hβ0 hβ1
  have hcL := intervalIntegrable_Lterm hβ0 hβ4
  have hcE := intervalIntegrable_Eterm hβ0 hβ2
  have hmL : (fun s : ℝ => (if s ≤ β then Lterm β s else Eterm β s))
      =ᵐ[volume.restrict (Set.uIoc (1/4) β)] (fun s : ℝ => Lterm β s) := by
    show ∀ᵐ s ∂volume.restrict (Set.uIoc (1/4) β),
      (if s ≤ β then Lterm β s else Eterm β s) = Lterm β s
    rw [ae_restrict_iff' (by rw [Set.uIoc_of_le hβ4]; exact measurableSet_Ioc)]
    exact Filter.Eventually.of_forall (fun s hs => by
      rw [Set.uIoc_of_le hβ4] at hs
      simp only [hs.2, if_true])
  have hmE : (fun s : ℝ => (if s ≤ β then Lterm β s else Eterm β s))
      =ᵐ[volume.restrict (Set.uIoc β (1/2))] (fun s : ℝ => Eterm β s) := by
    show ∀ᵐ s ∂volume.restrict (Set.uIoc β (1/2)),
      (if s ≤ β then Lterm β s else Eterm β s) = Eterm β s
    rw [ae_restrict_iff' (by rw [Set.uIoc_of_le hβ2]; exact measurableSet_Ioc)]
    exact Filter.Eventually.of_forall (fun s hs => by
      rw [Set.uIoc_of_le hβ2] at hs
      have : ¬ (s ≤ β) := by linarith [hs.1]
      simp only [this, if_false])
  have hcX1 : IntervalIntegrable (fun s : ℝ => (if s ≤ β then Lterm β s else Eterm β s))
      volume (1/4) β := hcL.congr_ae hmL.symm
  have hcE' : IntervalIntegrable (fun s : ℝ => Eterm β s) volume β (1/2) := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    rw [Set.uIcc_of_le hβ2] at hs
    have hs0 : (0:ℝ) < s := by linarith [hs.1, hβ4]
    apply ContinuousAt.continuousWithinAt
    simp only [Eterm]
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity)
  have hcX2 : IntervalIntegrable (fun s : ℝ => (if s ≤ β then Lterm β s else Eterm β s))
      volume β (1/2) := hcE'.congr_ae hmE.symm
  have hlin : (∫ s in (1/4:ℝ)..(1/2),
        (Tterm β s - N1term β s - (if s ≤ β then Lterm β s else Eterm β s)))
      = (∫ s in (1/4:ℝ)..(1/2), (Tterm β s - N1term β s))
        - ∫ s in (1/4:ℝ)..(1/2), (if s ≤ β then Lterm β s else Eterm β s) := by
    rw [intervalIntegral.integral_sub (hcT.sub hcN1) (hcX1.trans hcX2)]
  rw [hlin]
  have hlin2 : (∫ s in (1/4:ℝ)..(1/2), (Tterm β s - N1term β s))
      = (∫ s in (1/4:ℝ)..(1/2), Tterm β s) - ∫ s in (1/4:ℝ)..(1/2), N1term β s :=
    intervalIntegral.integral_sub hcT hcN1
  rw [hlin2]
  have hadj : (∫ s in (1/4:ℝ)..β, (if s ≤ β then Lterm β s else Eterm β s))
      + ∫ s in β..(1/2), (if s ≤ β then Lterm β s else Eterm β s)
      = ∫ s in (1/4:ℝ)..(1/2), (if s ≤ β then Lterm β s else Eterm β s) :=
    intervalIntegral.integral_add_adjacent_intervals hcX1 hcX2
  rw [← hadj]
  have hX1 : (∫ s in (1/4:ℝ)..β, (if s ≤ β then Lterm β s else Eterm β s))
      = ∫ s in (1/4:ℝ)..β, Lterm β s := by
    apply intervalIntegral.integral_congr_ae
    exact Filter.Eventually.of_forall (fun s hs => by
      rw [Set.uIoc_of_le hβ4] at hs
      simp only [hs.2, if_true])
  have hX2 : (∫ s in β..(1/2), (if s ≤ β then Lterm β s else Eterm β s))
      = ∫ s in β..(1/2), Eterm β s := by
    apply intervalIntegral.integral_congr_ae
    exact Filter.Eventually.of_forall (fun s hs => by
      rw [Set.uIoc_of_le hβ2] at hs
      have : ¬ (s ≤ β) := by linarith [hs.1]
      simp only [this, if_false])
  rw [hX1, hX2]
  have hT : (13/5)*(psi7 (dl1 β) + psi7 (dl2 β)) + Ctot β * psi7 (dlr β) + P4poly β + P5poly β
      ≤ ∫ s in (1/4:ℝ)..(1/2), Tterm β s := integral_T_term_ge hβ0 hβ2
  have hN : (∫ s in (1/4:ℝ)..(1/2), N1term β s) ≤ Real.log (2*(2-β)) * I0f β + stuff1f β :=
    integral_N1_le hβ0 hβ1
  have hI0 : 0 ≤ I0f β := by
    rw [I0f]
    have hh : 7/(768*(2-β)^2) ≤ 7/768 := by
      apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 7) (by norm_num : (0:ℝ) < 768)
      nlinarith [sq_nonneg (2-β), hβ4]
    linarith
  have hmul : Real.log (2*(2-β)) * I0f β ≤ LAf β * I0f β :=
    mul_le_mul_of_nonneg_right (log_2A_le_LAf hβ0 hβ1) hI0
  have hLb := integral_Lterm_le_Lb hβ4 hβ2
  have hEb := integral_Eterm_le_Eb hβ4 hβ2
  rw [Gh, G1]
  linarith [hT, hN, hmul, hLb, hEb]

/-! ## M. Region III and the final assembly -/

lemma FT_le_FF {β : ℝ} (hβ2 : (1:ℝ)/2 ≤ β) (hβ1 : β ≤ 1) : FT β ≤ FF β := by
  have h4 : P4poly β ≤ P4r β := P4poly_le hβ2 hβ1
  have h5 : P5poly β ≤ P5r β := P5poly_le hβ2 hβ1
  have h6 : stuff2f β ≤ S2poly β := stuff2f_le_S2poly hβ2 hβ1
  rw [FT, FF]
  linarith

theorem boxWindow_A0_lower_final {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (3:ℝ)/10 ≤ ∫ s in (1/4 : ℝ)..(1/2),
      ( (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
        + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
        + ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
        + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3)
        - Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s))*(1-s^2/(4*(2-β)^2))
        - (if s ≤ β then Real.log ((4*β^2+s^2)/(2*β*s))*(1-s^2/(2*((2-β)^2+β^2)))
                   else (2-β)*β/(s*Real.sqrt ((2-β)^2+s^2))) ) := by
  have hkey : (3:ℝ)/10 ≤ ∫ s in (1/4:ℝ)..(1/2),
      (Tterm β s - N1term β s - (if s ≤ β then Lterm β s else Eterm β s)) := by
    by_cases h4 : β ≤ 1/4
    · exact le_trans (G1_ge hβ0.le h4) (G1_le_integral hβ0 h4)
    · push_neg at h4
      by_cases h2 : β ≤ 1/2
      · exact le_trans (Gh_ge h4.le h2) (Gh_le_integral h4.le h2)
      · push_neg at h2
        have hFF : FF β ≤ ∫ s in (1/4:ℝ)..(1/2),
            (Tterm β s - N1term β s
              - Real.log ((4*β^2+s^2)/(2*β*s))*(1 - s^2/(2*((2-β)^2+β^2)))) :=
          integral_ge_FF hβ0 hβ1 h2.le
        have hFT : (3:ℝ)/10 ≤ FT β := FT_ge h2.le hβ1.le
        have hle : FT β ≤ FF β := FT_le_FF h2.le hβ1.le
        have hae : (∫ s in (1/4:ℝ)..(1/2),
            (Tterm β s - N1term β s
              - Real.log ((4*β^2+s^2)/(2*β*s))*(1 - s^2/(2*((2-β)^2+β^2)))))
            = ∫ s in (1/4:ℝ)..(1/2),
              (Tterm β s - N1term β s - (if s ≤ β then Lterm β s else Eterm β s)) := by
          apply intervalIntegral.integral_congr_ae
          exact Filter.Eventually.of_forall (fun s hs => by
            rw [Set.uIoc_of_le (by norm_num : (1:ℝ)/4 ≤ 1/2)] at hs
            have hs2 : s ≤ β := by linarith [hs.2, h2]
            simp only [Lterm, hs2, if_true])
        rw [hae] at hFF
        linarith
  simpa only [Tterm, N1term, Lterm, Eterm] using hkey

/-- Lower bound for the target-minus-majorant integral over `[1/4,1/2]`. -/
theorem boxWindow_A0_lower {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (3:ℝ)/10 ≤ ∫ s in (1/4 : ℝ)..(1/2),
      ( (13/5)*((3/2-β)/((3/2-β)^2+s^2)+(1+β)/((1+β)^2+s^2))
        + ((2-β)^2-β^2)/(2*((2-β)^2+s^2))
        + ((2-β)^2-β^2)^2/(8*((2-β)^2+s^2)^2)
        + ((2-β)^2-β^2)^3/(16*((2-β)^2+s^2)^3)
        - Real.log ((4*(2-β)^2+s^2)/(2*(2-β)*s))*(1-s^2/(4*(2-β)^2))
        - (if s ≤ β then Real.log ((4*β^2+s^2)/(2*β*s))*(1-s^2/(2*((2-β)^2+β^2)))
                   else (2-β)*β/(s*Real.sqrt ((2-β)^2+s^2))) ) := by
  exact boxWindow_A0_lower_final hβ0 hβ1

end Commons.Analysis.Integral

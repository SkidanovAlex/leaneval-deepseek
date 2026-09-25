import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Commons.Analysis.Fourier

open MeasureTheory

private lemma hasDerivAt_cexp_mul_one_add (c : ℂ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (fun z : ℝ => Complex.exp (c * (z : ℂ)) * ((1 + (z : ℂ)) / c - 1 / c ^ 2))
      (Complex.exp (c * (x : ℂ)) * (1 + (x : ℂ))) x := by
  have h1 : HasDerivAt (fun z : ℝ => Complex.exp (c * (z : ℂ))) (Complex.exp (c * (x:ℂ)) * c) x := by
    have hinner : HasDerivAt (fun z : ℝ => c * (z : ℂ)) (c * 1) x :=
      (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c
    have := hinner.cexp
    simpa using this
  have h2 : HasDerivAt (fun z : ℝ => (1 + (z : ℂ)) / c - 1 / c ^ 2) (1 / c) x := by
    have hnum : HasDerivAt (fun z : ℝ => (1:ℂ) + (z:ℂ)) (1 : ℂ) x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_add (1:ℂ)
    simpa using (hnum.div_const c).sub_const (1 / c ^ 2)
  have h := h1.mul h2
  have h' : HasDerivAt (fun z : ℝ => Complex.exp (c * (z:ℂ)) * ((1 + (z:ℂ))/c - 1/c^2))
      (Complex.exp (c*↑x) * c * ((1 + ↑x)/c - 1/c^2) + Complex.exp (c*↑x) * (1/c)) x := h
  rw [show Complex.exp (c*↑x) * c * ((1+↑x)/c - 1/c^2) + Complex.exp (c*↑x)*(1/c)
        = Complex.exp (c*↑x)*(1+↑x) from by field_simp; ring] at h'
  exact h'

private lemma hasDerivAt_cexp_mul_one_sub (c : ℂ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (fun z : ℝ => Complex.exp (c * (z : ℂ)) * ((1 - (z : ℂ)) / c + 1 / c ^ 2))
      (Complex.exp (c * (x : ℂ)) * (1 - (x : ℂ))) x := by
  have h1 : HasDerivAt (fun z : ℝ => Complex.exp (c * (z : ℂ))) (Complex.exp (c * (x:ℂ)) * c) x := by
    have hinner : HasDerivAt (fun z : ℝ => c * (z : ℂ)) (c * 1) x :=
      (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c
    have := hinner.cexp
    simpa using this
  have h2 : HasDerivAt (fun z : ℝ => (1 - (z : ℂ)) / c + 1 / c ^ 2) (-1 / c) x := by
    have hnum : HasDerivAt (fun z : ℝ => (1:ℂ) - (z:ℂ)) (-1 : ℂ) x := by
      have h := ((Complex.ofRealCLM.hasDerivAt (x := x))).const_sub (1:ℂ)
      simpa using h
    simpa using (hnum.div_const c).add_const (1 / c ^ 2)
  have h := h1.mul h2
  have h' : HasDerivAt (fun z : ℝ => Complex.exp (c * (z:ℂ)) * ((1 - (z:ℂ))/c + 1/c^2))
      (Complex.exp (c*↑x) * c * ((1 - ↑x)/c + 1/c^2) + Complex.exp (c*↑x) * (-1/c)) x := h
  rw [show Complex.exp (c*↑x) * c * ((1-↑x)/c + 1/c^2) + Complex.exp (c*↑x)*(-1/c)
        = Complex.exp (c*↑x)*(1-↑x) from by field_simp; ring] at h'
  exact h'

theorem triangle_kernel_fourier_transform :
    ∀ y : ℝ, ∫ x in (-1 : ℝ)..1, ((1 - |x| : ℝ) : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (y : ℂ) * (x : ℂ)))
      = ((if y = 0 then 1 else (Real.sin (Real.pi * y) / (Real.pi * y)) ^ 2 : ℝ) : ℂ) := by
  intro y
  by_cases hy : y = 0
  · subst hy
    have hexp : ∀ x : ℝ, -(2 * Real.pi * Complex.I * ((0:ℝ) : ℂ) * (x:ℂ)) = 0 := by intro x; simp
    simp only [hexp, Complex.exp_zero, mul_one, ↓reduceIte]
    rw [intervalIntegral.integral_ofReal, Complex.ofReal_inj]
    have h1 : (∫ x in (-1:ℝ)..0, (1 - |x|)) = 1/2 := by
      rw [show (∫ x in (-1:ℝ)..0, (1 - |x|)) = ∫ x in (-1:ℝ)..0, (1 + x) from by
        apply intervalIntegral.integral_congr
        intro x hx
        change (1 - |x|) = 1 + x
        have hx' : x ≤ 0 := (Set.mem_Icc.mp ((Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 0)) ▸ hx)).2
        simp [abs_of_nonpos hx']]
      have hder : ∀ t ∈ Set.uIcc (-1:ℝ) 0, HasDerivAt (fun s : ℝ => s + s^2/2) (1 + t) t := by
        intro t ht
        have h2 : HasDerivAt (fun s : ℝ => s^2/2) t t := by
          simpa using (hasDerivAt_id (x := t)).pow 2 |>.div_const 2
        exact (hasDerivAt_id (x := t)).add h2
      have hint : IntervalIntegrable (fun t : ℝ => 1 + t) volume (-1) 0 :=
        (by fun_prop : Continuous fun t : ℝ => 1 + t).intervalIntegrable _ _
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint]
      norm_num
    have h2 : (∫ x in (0:ℝ)..1, (1 - |x|)) = 1/2 := by
      rw [show (∫ x in (0:ℝ)..1, (1 - |x|)) = ∫ x in (0:ℝ)..1, (1 - x) from by
        apply intervalIntegral.integral_congr
        intro x hx
        change (1 - |x|) = 1 - x
        have hx' : 0 ≤ x := (Set.mem_Icc.mp ((Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)) ▸ hx)).1
        simp [abs_of_nonneg hx']]
      have hder : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun s : ℝ => s - s^2/2) (1 - t) t := by
        intro t ht
        have h2 : HasDerivAt (fun s : ℝ => s^2/2) t t := by
          simpa using (hasDerivAt_id (x := t)).pow 2 |>.div_const 2
        exact (hasDerivAt_id (x := t)).sub h2
      have hint : IntervalIntegrable (fun t : ℝ => 1 - t) volume 0 1 :=
        (by fun_prop : Continuous fun t : ℝ => 1 - t).intervalIntegrable _ _
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint]
      norm_num
    rw [← intervalIntegral.integral_add_adjacent_intervals
        ((by fun_prop : Continuous fun x : ℝ => 1 - |x|).intervalIntegrable (-1) 0)
        ((by fun_prop : Continuous fun x : ℝ => 1 - |x|).intervalIntegrable 0 1)]
    rw [h1, h2]; norm_num
  · simp only [if_neg hy]
    set c : ℂ := -(2 * Real.pi * Complex.I * (y : ℂ)) with hcdef
    have hc : c ≠ 0 := by
      rw [hcdef]; simp [Complex.ofReal_eq_zero, Real.pi_ne_zero, hy]
    have hexp : ∀ x : ℝ, -(2 * Real.pi * Complex.I * (y:ℂ) * (x:ℂ)) = c * (x:ℂ) := by
      intro x; rw [hcdef]; ring
    have hcont : Continuous fun x : ℝ => ((1 - |x| : ℝ) : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (y:ℂ) * (x:ℂ))) := by fun_prop
    have hneg : (∫ x in (-1:ℝ)..0, ((1 - |x| : ℝ) : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (y:ℂ) * (x:ℂ))))
        = 1/c - 1/c^2 + Complex.exp (-c)/c^2 := by
      rw [show (∫ x in (-1:ℝ)..0, ((1 - |x| : ℝ) : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (y:ℂ) * (x:ℂ))))
            = ∫ x in (-1:ℝ)..0, Complex.exp (c * (x:ℂ)) * (1 + (x:ℂ)) from by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp only
        have hx' : x ≤ 0 := (Set.mem_Icc.mp ((Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 0)) ▸ hx)).2
        rw [abs_of_nonpos hx', hexp x]
        push_cast
        ring]
      have hder : ∀ t ∈ Set.uIcc (-1:ℝ) 0, HasDerivAt (fun z : ℝ => Complex.exp (c * (z:ℂ)) * ((1 + (z:ℂ))/c - 1/c^2)) (Complex.exp (c * (t:ℂ)) * (1 + (t:ℂ))) t :=
        fun t _ => hasDerivAt_cexp_mul_one_add c hc t
      have hint : IntervalIntegrable (fun t : ℝ => Complex.exp (c * (t:ℂ)) * (1 + (t:ℂ))) volume (-1) 0 :=
        (by fun_prop : Continuous fun t : ℝ => Complex.exp (c * (t:ℂ)) * (1 + (t:ℂ))).intervalIntegrable _ _
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint]

      rw [show Complex.exp (c * ((0:ℝ):ℂ)) * ((1 + ((0:ℝ):ℂ))/c - 1/c^2) = 1/c - 1/c^2 from by simp,
          show Complex.exp (c * ((-1:ℝ):ℂ)) * ((1 + ((-1:ℝ):ℂ))/c - 1/c^2) = -Complex.exp (-c)/c^2 from by
            have hcm : c * ((-1:ℝ):ℂ) = -c := by push_cast; ring
            rw [hcm]; simp; ring]
      ring
    have hpos : (∫ x in (0:ℝ)..1, ((1 - |x| : ℝ) : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (y:ℂ) * (x:ℂ))))
        = Complex.exp c/c^2 - (1/c + 1/c^2) := by
      rw [show (∫ x in (0:ℝ)..1, ((1 - |x| : ℝ) : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (y:ℂ) * (x:ℂ))))
            = ∫ x in (0:ℝ)..1, Complex.exp (c * (x:ℂ)) * (1 - (x:ℂ)) from by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp only
        have hx' : 0 ≤ x := (Set.mem_Icc.mp ((Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)) ▸ hx)).1
        rw [abs_of_nonneg hx', hexp x]
        push_cast
        ring]
      have hder : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun z : ℝ => Complex.exp (c * (z:ℂ)) * ((1 - (z:ℂ))/c + 1/c^2)) (Complex.exp (c * (t:ℂ)) * (1 - (t:ℂ))) t :=
        fun t _ => hasDerivAt_cexp_mul_one_sub c hc t
      have hint : IntervalIntegrable (fun t : ℝ => Complex.exp (c * (t:ℂ)) * (1 - (t:ℂ))) volume 0 1 :=
        (by fun_prop : Continuous fun t : ℝ => Complex.exp (c * (t:ℂ)) * (1 - (t:ℂ))).intervalIntegrable _ _
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint]

      rw [show Complex.exp (c * ((1:ℝ):ℂ)) * ((1 - ((1:ℝ):ℂ))/c + 1/c^2) = Complex.exp c/c^2 from by
            rw [show c * ((1:ℝ):ℂ) = c from by simp, show (1:ℂ) - ((1:ℝ):ℂ) = 0 from by simp, zero_div, zero_add, one_div, div_eq_mul_inv],
          show Complex.exp (c * ((0:ℝ):ℂ)) * ((1 - ((0:ℝ):ℂ))/c + 1/c^2) = 1/c + 1/c^2 from by simp]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _), hneg, hpos]
    have hc1 : c = ((-(2*Real.pi*y) : ℝ) : ℂ) * Complex.I := by rw [hcdef]; push_cast; ring
    have hc2 : -c = (((2*Real.pi*y) : ℝ) : ℂ) * Complex.I := by rw [hcdef]; push_cast; ring
    have hI2 : Complex.I ^ 2 = -1 := by rw [pow_two, Complex.I_mul_I]
    have hsum : Complex.exp c + Complex.exp (-c) = ((2 * Real.cos (2*Real.pi*y) : ℝ) : ℂ) := by
      rw [hc2, hc1, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
      rw [Real.cos_neg, Real.sin_neg]
      push_cast
      ring
    have hcsq : c^2 = ((-(2*Real.pi*y)^2 : ℝ) : ℂ) := by
      rw [hc1, mul_pow, hI2]
      push_cast
      ring
    have hreal : (2 * Real.cos (2 * Real.pi * y) - 2) / (-((2 * Real.pi * y)^2)) = (Real.sin (Real.pi * y) / (Real.pi * y))^2 := by
      have hθ : (2 * Real.pi * y) = 2 * (Real.pi * y) := by ring
      rw [hθ, Real.cos_two_mul_eq_one_sub, div_pow]
      field_simp
      ring
    have hcombine : (1/c - 1/c^2 + Complex.exp (-c)/c^2) + (Complex.exp c/c^2 - (1/c + 1/c^2))
        = (((2 * Real.cos (2*Real.pi*y) - 2) / (-((2*Real.pi*y)^2)) : ℝ) : ℂ) := by
      have h1 : (1/c - 1/c^2 + Complex.exp (-c)/c^2) + (Complex.exp c/c^2 - (1/c + 1/c^2))
          = (Complex.exp c + Complex.exp (-c) - 2)/c^2 := by
        field_simp
        ring
      rw [h1, hsum, hcsq]
      push_cast
      ring
    rw [hcombine, hreal]

end Commons.Analysis.Fourier
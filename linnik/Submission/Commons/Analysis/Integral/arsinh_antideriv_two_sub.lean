import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Commons.Analysis.Integral

/-- The elementary antiderivative underlying the "box kernel" estimate:
`∫_0^2 (2-x)/√((x-a)²+t²) dx`
`= (2-a)(arsinh((2-a)/t) + arsinh(a/t)) - (√((2-a)²+t²) - √(a²+t²))`
for `t > 0`. -/
theorem arsinh_antideriv_two_sub (a t : ℝ) (ht : 0 < t) :
    (∫ x in (0:ℝ)..2, (2 - x)/Real.sqrt ((x-a)^2 + t^2))
      = (2-a)*(Real.arsinh ((2-a)/t) + Real.arsinh (a/t))
        - (Real.sqrt ((2-a)^2+t^2) - Real.sqrt (a^2+t^2)) := by
  set F : ℝ → ℝ := fun x => (2-a)*Real.arsinh ((x-a)/t) - Real.sqrt ((x-a)^2+t^2) with hFdef
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) 2, HasDerivAt F ((2-x)/Real.sqrt ((x-a)^2+t^2)) x := by
    intro x _
    simp only [hFdef]
    have htne : t ≠ 0 := ne_of_gt ht
    have hinner : HasDerivAt (fun x : ℝ => (x - a)/t) (1/t) x := by
      simpa using ((hasDerivAt_id x).sub_const a).div_const t
    have h1 : HasDerivAt (fun x : ℝ => Real.arsinh ((x-a)/t))
        ((Real.sqrt (1 + ((x-a)/t)^2))⁻¹ * (1/t)) x := by
      simpa using hinner.arsinh
    have h1' : HasDerivAt (fun x : ℝ => (2-a)*Real.arsinh ((x-a)/t))
        ((2-a) * ((Real.sqrt (1 + ((x-a)/t)^2))⁻¹ * (1/t))) x := h1.const_mul (2-a)
    have hinner2 : HasDerivAt (fun x : ℝ => (x-a)^2 + t^2) (2*(x-a)) x := by
      have h : HasDerivAt (fun x : ℝ => (x-a)^2 + t^2) (2 * (x - a) ^ (2 - 1) * 1) x :=
        (((hasDerivAt_id x).sub_const a).pow 2).add_const (t^2)
      simpa using h
    have hpos : (x-a)^2 + t^2 ≠ 0 := by positivity
    have h2 : HasDerivAt (fun x : ℝ => Real.sqrt ((x-a)^2+t^2))
        ((2*(x-a)) / (2*Real.sqrt ((x-a)^2+t^2))) x := hinner2.sqrt hpos
    have hF := h1'.sub h2
    have key : t * Real.sqrt (1 + ((x-a)/t)^2) = Real.sqrt ((x-a)^2+t^2) := by
      apply (sq_eq_sq₀ (mul_nonneg (le_of_lt ht) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)).mp
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      field_simp
      ring
    have hdeq : (2-a) * ((Real.sqrt (1 + ((x-a)/t)^2))⁻¹ * (1/t)) - (2*(x-a))/(2*Real.sqrt ((x-a)^2+t^2))
        = (2-x)/Real.sqrt ((x-a)^2+t^2) := by
      have hs : Real.sqrt ((x-a)^2+t^2) ≠ 0 := by positivity
      have hs1 : Real.sqrt (1 + ((x-a)/t)^2) ≠ 0 := by positivity
      rw [inv_mul_eq_div, ← key]
      field_simp
      ring
    exact hF.congr_deriv hdeq
  have hint : IntervalIntegrable (fun x => (2-x)/Real.sqrt ((x-a)^2+t^2)) MeasureTheory.volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    exact Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity)
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 2) hderiv hint
  rw [hmain]
  simp only [hFdef, zero_sub, neg_sq, neg_div, Real.arsinh_neg]
  ring

end Commons.Analysis.Integral
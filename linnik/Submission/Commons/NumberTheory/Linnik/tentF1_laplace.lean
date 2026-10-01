import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

open Complex
open scoped Interval

namespace Commons.NumberTheory.Linnik

/-- Derivative w.r.t. the real variable `y` of the complex exponential `cexp (c * y)`. -/
private lemma deriv_cexp_mul (c : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ))) (c * Complex.exp (c * (x : ℂ))) x := by
  have hinner : HasDerivAt (fun u : ℂ => c * u) c (x : ℂ) := by
    simpa using (hasDerivAt_id (x : ℂ)).const_mul c
  have hCe : HasDerivAt (fun u : ℂ => Complex.exp (c * u))
      (Complex.exp (c * (x : ℂ)) * c) (x : ℂ) := by
    exact HasDerivAt.comp (x : ℂ) (Complex.hasDerivAt_exp (c * (x : ℂ))) hinner
  exact (hCe.comp_ofReal).congr_deriv (by ring)

/-- Fundamental-theorem evaluation of `∫ cexp (c * t)`. -/
private lemma integral_exp_const (c : ℂ) (hc : c ≠ 0) (a b : ℝ) :
    (∫ t in a..b, Complex.exp (c * (t : ℂ))) =
      (Complex.exp (c * (b : ℂ)) - Complex.exp (c * (a : ℂ))) / c := by
  let F : ℝ → ℂ := fun y => Complex.exp (c * (y : ℂ)) / c
  let f' : ℝ → ℂ := fun y => Complex.exp (c * (y : ℂ))
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt F (f' x) x := by
    intro x hx
    have hE := deriv_cexp_mul c x
    dsimp [F, f']
    refine (hE.div_const c).congr_deriv ?_
    field_simp [hc]
  have hint : IntervalIntegrable f' MeasureTheory.volume a b := by
    have hc1 : Continuous f' := by fun_prop
    exact hc1.intervalIntegrable a b
  have hcalc : F b - F a = (Complex.exp (c * (b : ℂ)) - Complex.exp (c * (a : ℂ))) / c := by
    dsimp [F]
    field_simp [hc]
  rw [show (∫ t in a..b, Complex.exp (c * (t : ℂ))) = ∫ t in a..b, f' t by rfl]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  exact hcalc

/-- Same, with the lower endpoint `0`. -/
private lemma integral_exp_zero (c : ℂ) (hc : c ≠ 0) (b : ℝ) :
    (∫ t in (0 : ℝ)..b, Complex.exp (c * (t : ℂ))) =
      (Complex.exp (c * (b : ℂ)) - 1) / c := by
  rw [integral_exp_const c hc (0 : ℝ) b]
  congr 1
  norm_num

/-- The Laplace transform of `f₁(t) = sinh ((K − t)·x)` on `[0, K]` (Heath-Brown 1992,
§13, p. 81): with `z` away from `±x`,
`∫₀^K e^(−zt) sinh((K−t)x) dt = ½ { e^(xK)/(x+z) + e^(−xK)/(x−z) − 2x e^(−zK)/(x²−z²) }`. -/
theorem tentF1_laplace {K : ℝ} (hK : 0 < K) (x : ℝ) (hx : 0 < x) (z : ℂ)
    (hz1 : z ≠ (x : ℂ)) (hz2 : z ≠ -(x : ℂ)) :
    (∫ t in (0 : ℝ)..(K : ℝ),
        Complex.exp (-(z * (t : ℂ))) * ((Real.sinh ((K - t) * x) : ℝ) : ℂ)) =
      (1 / 2 : ℂ) * (Complex.exp (x * (K : ℂ)) / ((x : ℂ) + z) +
        Complex.exp (-(x * (K : ℂ))) / ((x : ℂ) - z) -
        2 * (x : ℂ) * Complex.exp (-(z * (K : ℂ))) / (((x : ℂ) ^ 2 - z ^ 2))) := by
  have hzp : (x : ℂ) + z ≠ 0 := by
    intro h
    apply hz2
    exact eq_neg_of_add_eq_zero_right h
  have hzm : (x : ℂ) - z ≠ 0 := by
    intro h
    exact hz1 (sub_eq_zero.mp h).symm
  have hsq : (x : ℂ) ^ 2 - z ^ 2 ≠ 0 := by
    intro h
    have hring : ((x : ℂ) + z) * ((x : ℂ) - z) = (x : ℂ) ^ 2 - z ^ 2 := by ring
    apply (mul_ne_zero hzp hzm)
    rwa [hring]
  let c1 : ℂ := -((x : ℂ) + z)
  let c2 : ℂ := (x : ℂ) - z
  have hc1 : c1 ≠ 0 := by dsimp [c1]; exact neg_ne_zero.mpr hzp
  have hc2 : c2 ≠ 0 := by dsimp [c2]; exact hzm
  set e1 : ℂ := Complex.exp ((x : ℂ) * (K : ℂ))
  set e2 : ℂ := Complex.exp (-((x : ℂ) * (K : ℂ)))
  set e3 : ℂ := Complex.exp (-(z * (K : ℂ)))
  let f : ℝ → ℂ := fun t => Complex.exp (-(z * (t : ℂ))) * ((Real.sinh ((K - t) * x) : ℝ) : ℂ)
  let X : ℝ → ℂ := fun t => e1 * Complex.exp (c1 * (t : ℂ))
  let Y : ℝ → ℂ := fun t => e2 * Complex.exp (c2 * (t : ℂ))
  -- pointwise identity on the interval: e^(−zt)·sinh((K−t)x) = ½(e1 e^(c1 t) − e2 e^(c2 t))
  have hpoint : Set.EqOn f (fun t => (X t - Y t) / 2) [[(0 : ℝ), K]] := by
    intro t ht
    dsimp [f, X, Y]
    rw [Complex.ofReal_sinh]
    simp [Complex.sinh]
    have h1 : Complex.exp (-(z * (t : ℂ))) *
        Complex.exp (((K : ℂ) - (t : ℂ)) * (x : ℂ)) = e1 * Complex.exp (c1 * (t : ℂ)) := by
      dsimp [e1, c1]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      ring
    have h2 : Complex.exp (-(z * (t : ℂ))) *
        Complex.exp (-(((K : ℂ) - (t : ℂ)) * (x : ℂ))) = e2 * Complex.exp (c2 * (t : ℂ)) := by
      dsimp [e2, c2]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      ring
    rw [← mul_div_assoc, mul_sub]
    rw [h1, h2]
  have hint_congr : (∫ t in (0 : ℝ)..(K : ℝ), f t) =
      ∫ t in (0 : ℝ)..(K : ℝ), (X t - Y t) / 2 := intervalIntegral.integral_congr hpoint
  -- integrability of X and Y
  have hintX : IntervalIntegrable X MeasureTheory.volume (0 : ℝ) K := by
    have hc : Continuous X := by
      dsimp [X]
      fun_prop
    exact hc.intervalIntegrable (0 : ℝ) K
  have hintY : IntervalIntegrable Y MeasureTheory.volume (0 : ℝ) K := by
    have hc : Continuous Y := by
      dsimp [Y]
      fun_prop
    exact hc.intervalIntegrable (0 : ℝ) K
  -- evaluate the integral of X : ∫ e^(xK)·e^(c1 t) = (e1 − e3)/(x + z)
  have hIX : (∫ t in (0 : ℝ)..(K : ℝ), X t) = (e1 - e3) / ((x : ℂ) + z) := by
    dsimp [X]
    rw [intervalIntegral.integral_const_mul]
    rw [integral_exp_zero c1 hc1 K]
    have he1e3 : e1 * Complex.exp (c1 * (K : ℂ)) = e3 := by
      dsimp [e1, e3, c1]
      rw [← Complex.exp_add]
      congr 1
      ring
    calc
      e1 * ((Complex.exp (c1 * (K : ℂ)) - 1) / c1)
          = (e1 * (Complex.exp (c1 * (K : ℂ)) - 1)) / c1 := by ring
      _ = (e1 * Complex.exp (c1 * (K : ℂ)) - e1) / c1 := by
          rw [mul_sub]
          ring
      _ = (e3 - e1) / c1 := by rw [he1e3]
      _ = (e1 - e3) / ((x : ℂ) + z) := by
          dsimp [c1]
          field_simp [hzp]
          ring
  -- evaluate the integral of Y : ∫ e^(−xK)·e^(c2 t) = (e3 − e2)/(x − z)
  have hIY : (∫ t in (0 : ℝ)..(K : ℝ), Y t) = (e3 - e2) / ((x : ℂ) - z) := by
    dsimp [Y]
    rw [intervalIntegral.integral_const_mul]
    rw [integral_exp_zero c2 hc2 K]
    have he2e3 : e2 * Complex.exp (c2 * (K : ℂ)) = e3 := by
      dsimp [e2, e3, c2]
      rw [← Complex.exp_add]
      congr 1
      ring
    calc
      e2 * ((Complex.exp (c2 * (K : ℂ)) - 1) / c2)
          = (e2 * (Complex.exp (c2 * (K : ℂ)) - 1)) / c2 := by ring
      _ = (e2 * Complex.exp (c2 * (K : ℂ)) - e2) / c2 := by
          rw [mul_sub]
          ring
      _ = (e3 - e2) / c2 := by rw [he2e3]
      _ = (e3 - e2) / ((x : ℂ) - z) := by
          simp [c2]
  -- assemble the integral of f
  have hIf : (∫ t in (0 : ℝ)..(K : ℝ), f t) =
      ((e1 - e3) / ((x : ℂ) + z) - (e3 - e2) / ((x : ℂ) - z)) / 2 := by
    rw [hint_congr]
    rw [intervalIntegral.integral_div]
    rw [intervalIntegral.integral_sub hintX hintY]
    rw [hIX, hIY]
  -- final assembly against the closed form
  rw [show (∫ t in (0 : ℝ)..(K : ℝ),
        Complex.exp (-(z * (t : ℂ))) * ((Real.sinh ((K - t) * x) : ℝ) : ℂ)) =
      ∫ t in (0 : ℝ)..(K : ℝ), f t by rfl]
  rw [hIf]
  field_simp [hzp, hzm, hsq]
  ring

end Commons.NumberTheory.Linnik
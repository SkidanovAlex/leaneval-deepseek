import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Calculus.Taylor.taylor_integral_remainder_two

/-!
# A second-order Taylor remainder bound with a `(1/2)` bilinear correction

For a function `f : E → ℝ` which is `C²` along the segment `{x + t • y | t ∈ [0,1]}`
and whose second Fréchet derivative is `ε`-close to a fixed continuous bilinear form
`B` on that segment, the second-order Taylor remainder with the `(1/2) B y y`
correction is bounded by `ε * ‖y‖ ^ 2`:

`|f (x + y) - f x - Df(x)·y - 1/2 * B y y| ≤ ε * ‖y‖ ^ 2`.

The proof uses the integral form of the Taylor remainder
(`Commons.Analysis.Calculus.Taylor.taylor_integral_remainder_two`),
`∫₀¹ (1 - t) dt = 1/2` to replace the constant `1/2 * B y y` by an integral,
and the elementary pointwise estimate `‖(D²f(z) - B) y y‖ ≤ ε * ‖y‖ ^ 2`.
-/

set_option linter.unusedVariables false

namespace Commons.Analysis.Calculus.Taylor

open MeasureTheory intervalIntegral
open scoped Topology

theorem abs_taylor_remainder_two_half_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x y : E} {B : E →L[ℝ] E →L[ℝ] ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ t ∈ Set.Icc (0:ℝ) 1, ContDiffAt ℝ 2 f (x + t • y))
    (hB : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖(fderiv ℝ (fderiv ℝ f)) (x + t • y) - B‖ ≤ ε) :
    |f (x + y) - f x - (fderiv ℝ f x) y - (1/2 : ℝ) * B y y| ≤ ε * ‖y‖ ^ 2 := by
  -- Taylor's theorem with integral remainder.
  have hrem := taylor_integral_remainder_two (f := f) (x := x) (y := y) hf
  -- Continuity of the second derivative along the segment, needed for integrability.
  have hD2 : ∀ t ∈ Set.Icc (0:ℝ) 1,
      ContinuousAt (fun s : ℝ => (fderiv ℝ (fderiv ℝ f)) (x + s • y)) t := by
    intro t ht
    have hct : ContinuousAt (fderiv ℝ (fderiv ℝ f)) (x + t • y) :=
      (((hf t ht).fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
        (by norm_num)).continuousAt
    exact hct.comp (f := fun s : ℝ => x + s • y) (x := t) (by fun_prop)
  -- `∫₀¹ (1 - t) dt = 1/2`.
  have hint : (∫ t in (0:ℝ)..1, (1 - t)) = 1/2 := by
    have h1 : IntervalIntegrable (fun t : ℝ => (1:ℝ)) volume (0:ℝ) 1 :=
      continuous_const.intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun t : ℝ => t) volume (0:ℝ) 1 :=
      continuous_id.intervalIntegrable _ _
    rw [intervalIntegral.integral_sub h1 h2, integral_one, integral_id]
    norm_num
  -- Hence `1/2 * B y y` is the integral of `(1 - t) * (B y y)`.
  have hI2 : (∫ t in (0:ℝ)..1, (1 - t) * (B y y)) = (1/2 : ℝ) * B y y := by
    rw [intervalIntegral.integral_mul_const, hint]
  -- Integrability of both integrands on `[0,1]`.
  have hg1 : IntervalIntegrable
      (fun t : ℝ => (1 - t) * (((fderiv ℝ (fderiv ℝ f)) (x + t • y)) y y)) volume (0:ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    intro t ht
    have h1 := hD2 t ht
    have h2 : ContinuousAt (fun s : ℝ => ((fderiv ℝ (fderiv ℝ f)) (x + s • y)) y) t :=
      h1.clm_apply continuousAt_const
    have h3 : ContinuousAt (fun s : ℝ => (((fderiv ℝ (fderiv ℝ f)) (x + s • y)) y) y) t :=
      h2.clm_apply continuousAt_const
    exact ((continuousAt_const.sub continuousAt_id).mul h3).continuousWithinAt
  have hg2 : IntervalIntegrable (fun t : ℝ => (1 - t) * (B y y)) volume (0:ℝ) 1 :=
    ((continuous_const.sub continuous_id).mul continuous_const).intervalIntegrable _ _
  -- The difference of the two integrands is `(1 - t) * (D²f - B)[y, y]` pointwise.
  have hJ : (∫ t in (0:ℝ)..1, ((1 - t) * (((fderiv ℝ (fderiv ℝ f)) (x + t • y)) y y)
        - (1 - t) * (B y y)))
      = ∫ t in (0:ℝ)..1, (1 - t) * ((((fderiv ℝ (fderiv ℝ f)) (x + t • y) - B) y) y) := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [sub_apply]
    ring
  -- The Taylor remainder equals the single integral above.
  have hEq : f (x + y) - f x - (fderiv ℝ f x) y - (1/2 : ℝ) * B y y
      = ∫ t in (0:ℝ)..1, (1 - t) * ((((fderiv ℝ (fderiv ℝ f)) (x + t • y) - B) y) y) := by
    rw [hrem]
    rw [show f x + (fderiv ℝ f x) y
          + (∫ t in (0:ℝ)..1, (1 - t) * (((fderiv ℝ (fderiv ℝ f)) (x + t • y)) y y))
          - f x - (fderiv ℝ f x) y - (1/2 : ℝ) * B y y
        = (∫ t in (0:ℝ)..1, (1 - t) * (((fderiv ℝ (fderiv ℝ f)) (x + t • y)) y y))
          - (1/2 : ℝ) * B y y by ring]
    rw [← hI2, ← intervalIntegral.integral_sub hg1 hg2]
    exact hJ
  rw [hEq]
  -- Pointwise bound on the integrand.
  have hbound : ∀ t ∈ Set.uIoc (0:ℝ) 1,
      ‖(1 - t) * ((((fderiv ℝ (fderiv ℝ f)) (x + t • y) - B) y) y)‖ ≤ ε * ‖y‖ ^ 2 := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at ht
    have htIcc : t ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
    have hD : ‖(((fderiv ℝ (fderiv ℝ f)) (x + t • y) - B) y) y‖ ≤ ε * ‖y‖ ^ 2 := by
      calc ‖(((fderiv ℝ (fderiv ℝ f)) (x + t • y) - B) y) y‖
          ≤ ‖((fderiv ℝ (fderiv ℝ f)) (x + t • y) - B) y‖ * ‖y‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (‖(fderiv ℝ (fderiv ℝ f)) (x + t • y) - B‖ * ‖y‖) * ‖y‖ :=
            mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg y)
        _ ≤ (ε * ‖y‖) * ‖y‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hB t htIcc) (norm_nonneg y)) (norm_nonneg y)
        _ = ε * ‖y‖ ^ 2 := by ring
    rw [norm_mul]
    have h1s : ‖(1:ℝ) - t‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2] : (0:ℝ) ≤ 1 - t)]
      linarith [ht.1]
    calc ‖(1:ℝ) - t‖ * ‖(((fderiv ℝ (fderiv ℝ f)) (x + t • y) - B) y) y‖
        ≤ 1 * (ε * ‖y‖ ^ 2) := mul_le_mul h1s hD (norm_nonneg _) (by norm_num)
      _ = ε * ‖y‖ ^ 2 := by ring
  -- Bound the integral.
  have hJle := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (C := ε * ‖y‖ ^ 2) hbound
  rw [Real.norm_eq_abs] at hJle
  calc |∫ t in (0:ℝ)..1, (1 - t) * ((((fderiv ℝ (fderiv ℝ f)) (x + t • y) - B) y) y)|
      ≤ (ε * ‖y‖ ^ 2) * |1 - (0:ℝ)| := hJle
    _ = ε * ‖y‖ ^ 2 := by rw [sub_zero, abs_one, mul_one]

end Commons.Analysis.Calculus.Taylor
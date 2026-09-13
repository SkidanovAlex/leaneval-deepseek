import Mathlib
import Submission.Commons.Analysis.Calculus.Taylor.taylor_integral_remainder_two

namespace Commons.Analysis.Calculus.Taylor

open MeasureTheory intervalIntegral
open scoped Topology

/-- Second-order Taylor formula with integral remainder, written relative to an arbitrary
continuous bilinear form `B`: for a function `f : E → ℝ` which is `C²` along the segment
`{x + t • y | t ∈ [0,1]}`,

`f (x + y) - f x - Df(x)·y - 1/2 * B y y = ∫₀¹ (1 - t) * ((D²f(x+t•y) - B) y y) dt`.

This is `Commons.Analysis.Calculus.Taylor.taylor_integral_remainder_two` combined with
`∫₀¹ (1 - t) dt = 1/2`. -/
theorem taylor_remainder_integral_two_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x y : E} {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hf : ∀ t ∈ Set.Icc (0:ℝ) 1, ContDiffAt ℝ 2 f (x + t • y)) :
    f (x + y) - f x - (fderiv ℝ f x) y - (1/2 : ℝ) * B y y
      = ∫ t in (0:ℝ)..1, (1 - t) * ((((fderiv ℝ (fderiv ℝ f)) (x + t • y) - B) y) y) := by
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
  rw [hrem]
  rw [show f x + (fderiv ℝ f x) y
        + (∫ t in (0:ℝ)..1, (1 - t) * (((fderiv ℝ (fderiv ℝ f)) (x + t • y)) y y))
        - f x - (fderiv ℝ f x) y - (1/2 : ℝ) * B y y
      = (∫ t in (0:ℝ)..1, (1 - t) * (((fderiv ℝ (fderiv ℝ f)) (x + t • y)) y y))
        - (1/2 : ℝ) * B y y by ring]
  rw [← hI2, ← intervalIntegral.integral_sub hg1 hg2]
  exact hJ

open MeasureTheory Metric Set Filter Function in
open scoped Topology ENNReal RealInnerProductSpace InnerProductSpace Convolution in
theorem taylor_two_remainder_integral {n : ℕ} {U : EuclideanSpace ℝ (Fin n) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {M₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (hU : ContDiff ℝ 2 U) (v : EuclideanSpace ℝ (Fin n)) :
    U (x₀ + v) - U x₀ - (fderiv ℝ U x₀) v - (1/2 : ℝ) * M₀ v v
      = ∫ t in (0:ℝ)..1, (1 - t) * ((fderiv ℝ (fderiv ℝ U) (x₀ + t • v) - M₀) v v) := by
  exact taylor_remainder_integral_two_sub (f := U) (x := x₀) (y := v) (B := M₀)
    (fun t _ => hU.contDiffAt)

end Commons.Analysis.Calculus.Taylor

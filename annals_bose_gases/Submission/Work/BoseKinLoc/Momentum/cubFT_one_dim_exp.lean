import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The one-dimensional Fourier transform of a symmetric window

`cubFT_one_dim_exp` identifies the complex integral
`∫_{−1/2}^{1/2} e^{i a t} dt` with the real integral `∫_{−1/2}^{1/2} cos (a t) dt`:
after `Complex.exp_ofReal_mul_I` the integrand splits into its cosine and sine parts, and the
sine part integrates to `0` because `t ↦ sin (a t)` is odd while the window `[−1/2, 1/2]` is
symmetric under `t ↦ −t` (`intervalIntegral.integral_comp_neg`).

The statement is the `c = 1/2` case of the general-window lemma `cubFT_one_dim_exp_general`,
which is recorded here because it is the same amount of work and applies to any symmetric
window.
-/

open MeasureTheory
open scoped Real

namespace Work.BoseKinLoc.Momentum

/-- `∫_{−c}^{c} sin (a t) dt = 0` for `c ≥ 0`: the integrand is odd and the window is
symmetric. -/
lemma cubFT_integral_sin_odd (a c : ℝ) (hc : 0 ≤ c) :
    ∫ t in Set.Icc (-c) c, Real.sin (a * t) = 0 := by
  -- Pass to the interval integral `∫_{−c}^{c}`, where the reflection lemma applies.
  have hconv : (∫ t in Set.Icc (-c) c, Real.sin (a * t))
      = ∫ t in (-c)..c, Real.sin (a * t) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -c ≤ c)]
  rw [hconv]
  -- `t ↦ −t` leaves `[−c, c]` invariant.
  have hsym : (∫ t in (-c)..c, Real.sin (a * (-t))) = ∫ t in (-c)..c, Real.sin (a * t) := by
    have h := intervalIntegral.integral_comp_neg (a := -c) (b := c)
      (f := fun t => Real.sin (a * t))
    simpa only [neg_neg] using h
  -- and turns the odd integrand into its negative.
  have hneg : (∫ t in (-c)..c, Real.sin (a * (-t)))
      = -(∫ t in (-c)..c, Real.sin (a * t)) := by
    rw [← intervalIntegral.integral_neg (f := fun t => Real.sin (a * t))]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [mul_neg, Real.sin_neg]
  linarith [hsym, hneg]

/-- Fourier transform of the indicator of `[−c, c]` (`c ≥ 0`): the complex exponential
integral equals the cosine integral. -/
lemma cubFT_one_dim_exp_general (a c : ℝ) (hc : 0 ≤ c) :
    ∫ t in Set.Icc (-c) c, Complex.exp (↑(a * t) * Complex.I)
      = ↑(∫ t in Set.Icc (-c) c, Real.cos (a * t)) := by
  have hsin : (∫ t in Set.Icc (-c) c, Real.sin (a * t)) = 0 := cubFT_integral_sin_odd a c hc
  -- Both summands are continuous on the compact window, hence integrable there.
  have hIc : Integrable (fun t : ℝ => (↑(Real.cos (a * t)) : ℂ))
      (volume.restrict (Set.Icc (-c) c)) :=
    ContinuousOn.integrableOn_compact isCompact_Icc (by fun_prop)
  have hIs : Integrable (fun t : ℝ => (↑(Real.sin (a * t)) : ℂ) * Complex.I)
      (volume.restrict (Set.Icc (-c) c)) :=
    ContinuousOn.integrableOn_compact isCompact_Icc (by fun_prop)
  -- Split the exponential into its real and imaginary parts.
  have hpoint : ∀ t : ℝ, Complex.exp (↑(a * t) * Complex.I)
      = (↑(Real.cos (a * t)) : ℂ) + ↑(Real.sin (a * t)) * Complex.I :=
    fun t => Complex.exp_ofReal_mul_I _
  rw [show (∫ t in Set.Icc (-c) c, Complex.exp (↑(a * t) * Complex.I))
      = ∫ t in Set.Icc (-c) c,
          ((↑(Real.cos (a * t)) : ℂ) + ↑(Real.sin (a * t)) * Complex.I) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun t _ => hpoint t)]
  rw [MeasureTheory.integral_add hIc hIs, MeasureTheory.integral_mul_const]
  -- Push the real-to-complex coercion out of each integral and kill the sine term.
  have h1 : (∫ t in Set.Icc (-c) c, (↑(Real.cos (a * t)) : ℂ))
      = ↑(∫ t in Set.Icc (-c) c, Real.cos (a * t)) := integral_ofReal
  have h2 : (∫ t in Set.Icc (-c) c, (↑(Real.sin (a * t)) : ℂ))
      = ↑(∫ t in Set.Icc (-c) c, Real.sin (a * t)) := integral_ofReal
  rw [h1, h2, hsin]
  simp

theorem cubFT_one_dim_exp (a : ℝ) :
    ∫ t in Set.Icc (-(1:ℝ) / 2) ((1:ℝ) / 2), Complex.exp (↑(a * t) * Complex.I)
      = ↑(∫ t in Set.Icc (-(1:ℝ) / 2) ((1:ℝ) / 2), Real.cos (a * t)) := by
  -- Rewrite the window `[−(1/2), 1/2]` in the shape `[−c, c]` with `c = 1/2`
  -- (the two left endpoints are equal but not syntactically identical).
  have hset : Set.Icc (-(1:ℝ) / 2) ((1:ℝ) / 2) = Set.Icc (-((1:ℝ) / 2)) ((1:ℝ) / 2) := by
    congr 1
    ring
  rw [hset]
  exact cubFT_one_dim_exp_general a ((1:ℝ) / 2) (by norm_num)

end Work.BoseKinLoc.Momentum

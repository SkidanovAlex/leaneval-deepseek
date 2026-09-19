import Mathlib.Analysis.Complex.CauchyIntegral
import Submission.Commons.Analysis.Complex.zeroFactor_g
import Submission.Commons.Analysis.Complex.log_boundary_factor

open Complex MeasureTheory intervalIntegral MeromorphicOn
open scoped Real Interval Topology
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Commons.Analysis.Complex

/-- A point of the divisor support of an analytic function is a zero of the function. -/
lemma divisor_ne_zero_imp_eq_zero_of_analyticOnNhd {f : ℂ → ℂ} {R : ℝ}
    (hfB : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R)) {u : ℂ}
    (hD : (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R)) u ≠ 0) : f u = 0 := by
  by_contra hfu
  have huB : u ∈ Metric.closedBall (0 : ℂ) R := by
    by_contra hout
    apply hD
    rw [MeromorphicOn.divisor_def]
    simp [hout]
  have hord : meromorphicOrderAt f u = 0 :=
    meromorphicOrderAt_eq_zero_of_ne_zero (hfB u huB) hfu
  apply hD
  rw [MeromorphicOn.divisor_apply hfB.meromorphicOn huB]
  simp [hord]

/-- **Argument-principle zero count in a rectangle, bounded by the four side integrals of
`|f'/f|`.**

`f : ℂ → ℂ` is entire, does not vanish on the closed rectangle with corners `z`, `w`
(`z.re < w.re`, `z.im < w.im`), `f 0 ≠ 0`, and the whole closed rectangle lies inside
`ball 0 R`.  Then the weighted count of zeros *strictly inside* the open rectangle,
counted with the multiplicity given by the divisor of `f` on `closedBall 0 R`, is at most
`(2π)⁻¹` times the sum of the four side integrals of `‖logDeriv f‖` over the boundary of the
rectangle.

Proof outline (argument principle): (1) on a neighbourhood of the closed rectangle factor
`f = P · g` with `P s = ∏ᶠ u, (s-u) ^ divisor u` over the finitely many zeros strictly inside,
`g` holomorphic and nonzero there (adapt `Commons.Analysis.Complex.zeroFactor_g` /
the factorization machinery of `Commons.NumberTheory.Linnik.logDeriv_circle_residue` from
balls to rectangles, or apply it on a large ball and restrict); then
`logDeriv f = ∑ᶠ u, divisor u · (s-u)⁻¹ + logDeriv g` on the boundary, the `logDeriv g` term
integrates to `0` by `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`, and the
rectangular integral of each `(s-u)⁻¹` is `2πi` if `u` is strictly inside and `0` if outside
by `Commons.Analysis.Complex.rectIntegral_sub_inv_inside` / `_outside`.  This gives the exact
identity; (2) bound the norm of the identity by the norm of `(2πi)⁻¹` times the four side
integrals, each `≤` the integral of the norm of the integrand
(`intervalIntegral.norm_integral_le_of_norm_le` style). -/
theorem rectZeroCount_le {f : ℂ → ℂ} {z w : ℂ} {R : ℝ}
    (hfdiff : Differentiable ℂ f) (hRpos : 0 < R) (hzre : z.re < w.re) (hzim : z.im < w.im)
    (hf0 : f 0 ≠ 0)
    (hrect : ∀ s : ℂ, z.re ≤ s.re → s.re ≤ w.re → z.im ≤ s.im → s.im ≤ w.im → ‖s‖ < R)
    (hfne : ∀ s : ℂ, z.re ≤ s.re → s.re ≤ w.re → z.im ≤ s.im → s.im ≤ w.im → f s ≠ 0) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ) *
        (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then 1 else 0)) ≤
      (1 / (2 * Real.pi)) *
        ((∫ x : ℝ in z.re..w.re, ‖logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I)‖) +
         (∫ x : ℝ in z.re..w.re, ‖logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I)‖) +
         (∫ y : ℝ in z.im..w.im, ‖logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I)‖) +
         (∫ y : ℝ in z.im..w.im, ‖logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I)‖)) := by
  classical
  have hfB : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R) := by
    intro z hz
    exact hfdiff.analyticAt z
  -- Since `f` is non-zero on the whole closed rectangle, it has no zeros (hence no divisor
  -- support) strictly inside the open rectangle: every summand of the left hand side vanishes.
  have hD0_of_inside : ∀ u : ℂ,
      z.re < u.re → u.re < w.re → z.im < u.im → u.im < w.im →
      (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R)) u = 0 := by
    intro u h1 h2 h3 h4
    by_contra hD
    have hfz : f u = 0 := divisor_ne_zero_imp_eq_zero_of_analyticOnNhd hfB hD
    have hfnz : f u ≠ 0 := hfne u (le_of_lt h1) (le_of_lt h2) (le_of_lt h3) (le_of_lt h4)
    exact hfnz hfz
  have hterm0 : ∀ u : ℂ,
      (((MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ) *
        (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then 1 else 0) = 0 := by
    intro u
    by_cases hc : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im
    · have hdu0 : (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R)) u = 0 :=
        hD0_of_inside u hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
      simp [hc, hdu0]
    · simp [hc]
  have hLHS0 : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ) *
        (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then 1 else 0)) = 0 := by
    have hfun : (fun u : ℂ => (((MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ) *
        (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then 1 else 0)) =
        (fun _ : ℂ => (0 : ℝ)) := by
      funext u
      exact hterm0 u
    rw [hfun]
    simp
  rw [hLHS0]
  -- The right hand side is non-negative: it is `(2π)⁻¹` times the sum of four integrals of
  -- non-negative integrands over left-to-right intervals.
  have hx : z.re ≤ w.re := le_of_lt hzre
  have hy : z.im ≤ w.im := le_of_lt hzim
  have hI1 : 0 ≤ ∫ x : ℝ in z.re..w.re, ‖logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I)‖ :=
    intervalIntegral.integral_nonneg hx (fun x hxmem => norm_nonneg _)
  have hI2 : 0 ≤ ∫ x : ℝ in z.re..w.re, ‖logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I)‖ :=
    intervalIntegral.integral_nonneg hx (fun x hxmem => norm_nonneg _)
  have hI3 : 0 ≤ ∫ y : ℝ in z.im..w.im, ‖logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I)‖ :=
    intervalIntegral.integral_nonneg hy (fun y hymem => norm_nonneg _)
  have hI4 : 0 ≤ ∫ y : ℝ in z.im..w.im, ‖logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I)‖ :=
    intervalIntegral.integral_nonneg hy (fun y hymem => norm_nonneg _)
  have hsum : 0 ≤
      ((∫ x : ℝ in z.re..w.re, ‖logDeriv f ((x : ℂ) + (z.im : ℂ) * Complex.I)‖) +
       (∫ x : ℝ in z.re..w.re, ‖logDeriv f ((x : ℂ) + (w.im : ℂ) * Complex.I)‖) +
       (∫ y : ℝ in z.im..w.im, ‖logDeriv f ((w.re : ℂ) + (y : ℂ) * Complex.I)‖) +
       (∫ y : ℝ in z.im..w.im, ‖logDeriv f ((z.re : ℂ) + (y : ℂ) * Complex.I)‖)) := by
    nlinarith
  have h2pi : 0 < (2 : ℝ) * Real.pi := by
    exact mul_pos (by norm_num) Real.pi_pos
  have hcoef : 0 ≤ (1 : ℝ) / (2 * Real.pi) := (div_pos (by norm_num) h2pi).le
  exact mul_nonneg hcoef hsum

end Commons.Analysis.Complex
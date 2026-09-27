import Mathlib
import Submission.Work.Mostow.localIsomDefs
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.Hyper

/-!
# Auxiliary lemmas for the convexity of hyperbolic balls

Elementary real-analytic and chart facts used by `Work.Mostow.ballConvex`:

* `sinhSqAdd` — the hyperbolic double-angle identity
  `sinh(a+b)² = sinh a² + sinh b² + 2 sinh a sinh b cosh(a+b)`;
* `hdistPosOfNe` — distinct points are at strictly positive hyperbolic distance;
* `sinhSegLe` — `sinh(d-s) + sinh s ≤ sinh d` for `s ∈ [0,d]`;
* `coshMax` — `cosh` commutes with `max` on the nonnegative reals.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- The hyperbolic double-angle identity in the form needed for the Minkowski norm of a
convex combination of two lifts. -/
theorem sinhSqAdd (a b : ℝ) : Real.sinh (a + b) ^ 2 = Real.sinh a ^ 2 + Real.sinh b ^ 2
      + 2 * Real.sinh a * Real.sinh b * Real.cosh (a + b) := by
  have h1 : Real.sinh (a + b) ^ 2 = Real.cosh (a + b) ^ 2 - 1 := by rw [Real.sinh_sq]
  rw [h1, Real.cosh_add]
  have h2 := Real.cosh_sq a
  have h3 := Real.cosh_sq b
  have h4 : Real.sinh a ^ 2 = Real.cosh a ^ 2 - 1 := Real.sinh_sq a
  have h5 : Real.sinh b ^ 2 = Real.cosh b ^ 2 - 1 := Real.sinh_sq b
  nlinarith [h2, h3, h4, h5]

/-- Distinct points of hyperbolic space are at strictly positive distance. -/
theorem hdistPosOfNe {n : ℕ} {u v : E n} (h : u ≠ v) : 0 < hdist u v := by
  refine lt_of_le_of_ne (hdist_nonneg u v) ?_
  intro h0
  apply h
  have hcd : tpart u * tpart v - inner ℝ u v = 1 := by
    have hh := cosh_hdist u v
    rw [← h0, Real.cosh_zero] at hh
    exact hh.symm
  have hns : ‖tpart v • u - tpart u • v‖ ^ 2 = -(tpart u - tpart v) ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt (tpart_pos v)), abs_of_nonneg (le_of_lt (tpart_pos u)),
        real_inner_smul_left, real_inner_smul_right]
    nlinarith [hcd, tpart_sq u, tpart_sq v]
  have hzero : (tpart u - tpart v) ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖tpart v • u - tpart u • v‖, hns]
  have htveq : tpart u = tpart v := sub_eq_zero.mp (sq_eq_zero_iff.mp hzero)
  have hzeq : tpart v • u - tpart u • v = 0 := by
    have h2 : ‖tpart v • u - tpart u • v‖ = 0 :=
      sq_eq_zero_iff.mp (by rw [hns, hzero]; ring)
    exact norm_eq_zero.mp h2
  have key : tpart v • u = tpart u • v := sub_eq_zero.mp hzeq
  have key2 : tpart v • u = tpart v • v := by rw [key, htveq]
  exact smul_right_injective (E n) (ne_of_gt (tpart_pos v)) key2

/-- `sinh` is subadditive along a segment: `sinh (d - s) + sinh s ≤ sinh d` for `0 ≤ s ≤ d`. -/
theorem sinhSegLe {d s : ℝ} (hs : s ∈ Set.Icc 0 d) :
    Real.sinh (d - s) + Real.sinh s ≤ Real.sinh d := by
  have hs0 : 0 ≤ s := hs.1
  have hds0 : 0 ≤ d - s := by linarith [hs.2]
  have h1 : Real.sinh (d - s) ≤ Real.sinh (d - s) * Real.cosh s := by
    nlinarith [Real.sinh_nonneg_iff.mpr hds0, Real.one_le_cosh s]
  have h2 : Real.sinh s ≤ Real.cosh (d - s) * Real.sinh s := by
    nlinarith [Real.sinh_nonneg_iff.mpr hs0, Real.one_le_cosh (d - s)]
  have hsinh : Real.sinh d =
      Real.sinh (d - s) * Real.cosh s + Real.cosh (d - s) * Real.sinh s := by
    conv_lhs => rw [show d = (d - s) + s from by ring]
    rw [Real.sinh_add]
  rw [hsinh]
  linarith

/-- On the nonnegative reals `cosh` commutes with `max`. -/
theorem coshMax {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.cosh (max a b) = max (Real.cosh a) (Real.cosh b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h,
      max_eq_right (by rw [Real.cosh_le_cosh]; simpa [abs_of_nonneg ha, abs_of_nonneg hb] using h)]
  · rw [max_eq_left h,
      max_eq_left (by rw [Real.cosh_le_cosh]; simpa [abs_of_nonneg ha, abs_of_nonneg hb] using h)]

end Work.Mostow

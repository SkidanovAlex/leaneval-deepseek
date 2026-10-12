import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Submission.Work.BoseBoxFock.SqrtKinDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.SqrtKin.heatK_rpow_integrableOn`

The function `t ↦ t ^ (-(3 : ℝ) / 2) * heatK t z` is integrable on `(0, ∞)` for `z ≠ 0`.

Indeed (this is `heatK_mul_rpow_eq` below)

`t^{-3/2} · heatK t z = (4π)^{-3/2} · t^{-3} · exp(-(c/t))`,  with  `c = ‖z‖²/4 > 0`,

so the claim is the elementary fact that `t ↦ t^a exp(-c/t)` is integrable on `(0, ∞)` for
`a < -1` and `c > 0` (`integrableOn_rpow_mul_exp_neg_div`). That fact is proved by the
substitution `t = x^{-2}` (`integrableOn_Ioi_comp_rpow_iff`), which turns `t^a exp(-c/t)` into
`x^{-2a-3} exp(-c x²)`, a polynomial times a Gaussian — integrable by
`integrableOn_rpow_mul_exp_neg_mul_sq`.

The hypothesis `z ≠ 0` (i.e. `c > 0`) cannot be dropped: for `z = 0` the integrand reduces to
`(4π)^{-3/2} t^{-3}`, which is not integrable at `0`.

This is the integrability input for the sibling evaluation
`∫_{t>0} t^{-3/2} heatK t z dt = 2/(π^{3/2}‖z‖⁴)`.
-/

namespace Work.BoseBoxFock.SqrtKin

open MeasureTheory

/-- The elementary `t`-integrand `t ^ a · exp (-(c / t))` is integrable on `(0, ∞)` whenever
`a < -1` and `c > 0`. -/
lemma integrableOn_rpow_mul_exp_neg_div {a c : ℝ} (ha : a < -1) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ a * Real.exp (-(c / t))) (Set.Ioi 0) := by
  -- substitute `t = x ^ (-2)`
  rw [← integrableOn_Ioi_comp_rpow_iff (f := fun t : ℝ => t ^ a * Real.exp (-(c / t)))
    (p := (-2 : ℝ)) (by norm_num)]
  refine (integrableOn_congr_fun (s := Set.Ioi (0 : ℝ))
    (f := fun x : ℝ =>
      (|(-2 : ℝ)| * x ^ ((-2 : ℝ) - 1)) • ((x ^ (-2 : ℝ)) ^ a * Real.exp (-(c / x ^ (-2 : ℝ)))))
    (g := fun x : ℝ => 2 * (x ^ (-2 * a - 3) * Real.exp (-c * x ^ 2)))
    (fun x hx => ?_) measurableSet_Ioi).mpr ?_
  · -- the substituted integrand is `2 * x^(-2a-3) * exp(-c x²)`
    have hx0 : 0 < x := hx
    have hx2 : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hx.le, Real.rpow_two]
    have h3 : c / x ^ (-2 : ℝ) = c * x ^ 2 := by rw [hx2, div_inv_eq_mul]
    calc (|(-2 : ℝ)| * x ^ ((-2 : ℝ) - 1)) •
            ((x ^ (-2 : ℝ)) ^ a * Real.exp (-(c / x ^ (-2 : ℝ))))
        = 2 * (x ^ (-3 : ℝ) * (x ^ (-2 : ℝ)) ^ a) * Real.exp (-c * x ^ 2) := by
          rw [abs_of_neg (by norm_num : (-2 : ℝ) < 0), show (-2 : ℝ) - 1 = -3 by norm_num,
            smul_eq_mul, h3, neg_mul]
          ring_nf
      _ = 2 * (x ^ (-3 : ℝ) * x ^ ((-2 : ℝ) * a)) * Real.exp (-c * x ^ 2) := by
          rw [← Real.rpow_mul hx.le]
      _ = 2 * x ^ ((-3 : ℝ) + (-2 : ℝ) * a) * Real.exp (-c * x ^ 2) := by
          rw [← Real.rpow_add hx0]
      _ = 2 * (x ^ (-2 * a - 3) * Real.exp (-c * x ^ 2)) := by
          rw [show (-3 : ℝ) + (-2 : ℝ) * a = -2 * a - 3 by ring]
          ring_nf
  · -- `x ^ (-2a-3) exp(-c x²)` is a polynomial times a Gaussian, with exponent `-2a-3 > -1`
    exact (integrableOn_rpow_mul_exp_neg_mul_sq hc (s := -2 * a - 3) (by linarith)).const_mul 2

/-- The explicit form of the integrand: `t^{-3/2} heatK t z = (4π)^{-3/2} t^{-3} exp(-(c/t))`
with `c = ‖z‖²/4`. -/
lemma heatK_mul_rpow_eq (t : ℝ) (ht : 0 < t) (z : EuclideanSpace ℝ (Fin 3)) :
    t ^ (-(3 : ℝ) / 2) * heatK t z
      = (4 * Real.pi) ^ (-(3 : ℝ) / 2) * (t ^ (-(3 : ℝ)) * Real.exp (-(‖z‖ ^ 2 / 4 / t))) := by
  have h4 : (0 : ℝ) ≤ 4 * Real.pi := by positivity
  have h1 : (4 * Real.pi * t) ^ (-(3 : ℝ) / 2)
      = (4 * Real.pi) ^ (-(3 : ℝ) / 2) * t ^ (-(3 : ℝ) / 2) := Real.mul_rpow h4 ht.le
  have h2 : t ^ (-(3 : ℝ) / 2) * t ^ (-(3 : ℝ) / 2) = t ^ (-(3 : ℝ)) := by
    rw [← Real.rpow_add ht]; norm_num
  have h3 : ‖z‖ ^ 2 / (4 * t) = ‖z‖ ^ 2 / 4 / t := by ring
  calc t ^ (-(3 : ℝ) / 2) * heatK t z
      = t ^ (-(3 : ℝ) / 2) *
          ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * Real.exp (-(‖z‖ ^ 2 / (4 * t)))) := by
        rw [show heatK t z
            = (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * Real.exp (-(‖z‖ ^ 2 / (4 * t))) from rfl]
    _ = t ^ (-(3 : ℝ) / 2) *
          (((4 * Real.pi) ^ (-(3 : ℝ) / 2) * t ^ (-(3 : ℝ) / 2))
            * Real.exp (-(‖z‖ ^ 2 / (4 * t)))) := by rw [h1]
    _ = (4 * Real.pi) ^ (-(3 : ℝ) / 2) *
          ((t ^ (-(3 : ℝ) / 2) * t ^ (-(3 : ℝ) / 2))
            * Real.exp (-(‖z‖ ^ 2 / (4 * t)))) := by ring
    _ = (4 * Real.pi) ^ (-(3 : ℝ) / 2) * (t ^ (-(3 : ℝ)) * Real.exp (-(‖z‖ ^ 2 / (4 * t)))) := by
        rw [h2]
    _ = (4 * Real.pi) ^ (-(3 : ℝ) / 2) * (t ^ (-(3 : ℝ)) * Real.exp (-(‖z‖ ^ 2 / 4 / t))) := by
        rw [h3]

theorem heatK_rpow_integrableOn {z : EuclideanSpace ℝ (Fin 3)} (hz : z ≠ 0) :
    IntegrableOn (fun t : ℝ => t ^ (-(3 : ℝ) / 2) * heatK t z) (Set.Ioi 0) := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hc : 0 < ‖z‖ ^ 2 / 4 := div_pos (pow_pos hzn 2) (by norm_num)
  have hpure : IntegrableOn (fun t : ℝ => t ^ (-(3 : ℝ)) * Real.exp (-(‖z‖ ^ 2 / 4 / t)))
      (Set.Ioi 0) := integrableOn_rpow_mul_exp_neg_div (by norm_num : (-(3 : ℝ)) < -1) hc
  refine (integrableOn_congr_fun (s := Set.Ioi (0 : ℝ))
    (f := fun t : ℝ => t ^ (-(3 : ℝ) / 2) * heatK t z)
    (g := fun t : ℝ =>
      (4 * Real.pi) ^ (-(3 : ℝ) / 2) * (t ^ (-(3 : ℝ)) * Real.exp (-(‖z‖ ^ 2 / 4 / t))))
    (fun t ht => heatK_mul_rpow_eq t ht z) measurableSet_Ioi).mpr ?_
  exact hpure.const_mul _

end Work.BoseBoxFock.SqrtKin

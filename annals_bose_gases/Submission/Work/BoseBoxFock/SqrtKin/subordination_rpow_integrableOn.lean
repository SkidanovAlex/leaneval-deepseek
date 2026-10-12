import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of the subordination kernel `t ↦ (1 − e^{−a t}) t^{−3/2}` on `(0, ∞)`

The per-mode subordination identity of the heat-kernel representation of `√(−Δ)` is

  `∫_0^∞ (1 − e^{−a t}) t^{−3/2} dt = 2√π·√a`   (`a ≥ 0`);

this file proves the integrability side condition that makes the integral meaningful.

Near `0` the factor `1 − e^{−a t}` is `O(t)`, so the integrand is dominated by the summable
`t ↦ a t^{−1/2}`; the tail is dominated by `t ↦ t^{−3/2}`, which is summable on `(1, ∞)`.
The two pieces are glued with `Ioi 0 = Ioc 0 1 ∪ Ioi 1`.
-/

namespace Work.BoseBoxFock.SqrtKin

open MeasureTheory

/-- `t ↦ t^{−1/2}` is integrable on `(0, 1]` (integrable singularity at `0`), via
`intervalIntegral.intervalIntegrable_rpow'` in the range `−1 < r`. -/
private theorem integrableOn_Ioc_rpow_neg_half_aux :
    IntegrableOn (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) (Set.Ioc 0 1) volume := by
  have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
    (r := -(1 : ℝ) / 2) (by norm_num)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
  exact h

/-- `t ↦ t^{−3/2}` is integrable on `(1, ∞)` (`−3/2 < −1`). -/
private theorem integrableOn_Ioi_rpow_neg_three_halves_aux :
    IntegrableOn (fun t : ℝ => t ^ (-(3 : ℝ) / 2)) (Set.Ioi 1) volume := by
  rw [integrableOn_Ioi_rpow_iff (by norm_num : (0 : ℝ) < 1)]
  norm_num

/-- **The near-`0` piece**: on `(0, 1]` the integrand is dominated by `a t^{−1/2}`, because
`1 − e^{−a t} ≤ a t` for `a, t ≥ 0` (`Real.one_sub_le_exp_neg`). -/
private theorem integrableOn_Ioc_one_sub_exp_aux (a : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (fun t : ℝ => (1 - Real.exp (-(a * t))) * t ^ (-(3 : ℝ) / 2))
      (Set.Ioc 0 1) := by
  have hmaj : Integrable (fun t : ℝ => a * t ^ (-(1 : ℝ) / 2))
      (volume.restrict (Set.Ioc 0 1)) :=
    integrableOn_Ioc_rpow_neg_half_aux.const_mul a
  refine Integrable.mono' hmaj ?_ ?_
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := ht.1
    have h1 : 0 ≤ 1 - Real.exp (-(a * t)) := by
      have h : Real.exp (-(a * t)) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith [ha, ht0.le])
      simpa using h
    have h2 : 1 - Real.exp (-(a * t)) ≤ a * t := by
      have h := Real.one_sub_le_exp_neg (a * t); linarith
    have h3 : 0 ≤ t ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg ht0.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h3)]
    calc (1 - Real.exp (-(a * t))) * t ^ (-(3 : ℝ) / 2)
        ≤ (a * t) * t ^ (-(3 : ℝ) / 2) := mul_le_mul_of_nonneg_right h2 h3
      _ = a * t ^ (-(1 : ℝ) / 2) := by
          rw [show (a * t) * t ^ (-(3 : ℝ) / 2)
                = a * (t ^ (1 : ℝ) * t ^ (-(3 : ℝ) / 2)) by
                rw [Real.rpow_one]; ring,
              ← Real.rpow_add ht0,
              show (1 : ℝ) + (-(3 : ℝ) / 2) = -(1 : ℝ) / 2 by norm_num]

/-- **The tail piece**: on `(1, ∞)` the integrand is dominated by `t^{−3/2}`, because
`0 ≤ 1 − e^{−a t} ≤ 1` there. -/
private theorem integrableOn_Ioi_one_sub_exp_aux (a : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (fun t : ℝ => (1 - Real.exp (-(a * t))) * t ^ (-(3 : ℝ) / 2))
      (Set.Ioi 1) := by
  have hmaj : Integrable (fun t : ℝ => t ^ (-(3 : ℝ) / 2))
      (volume.restrict (Set.Ioi 1)) :=
    integrableOn_Ioi_rpow_neg_three_halves_aux
  refine Integrable.mono' hmaj ?_ ?_
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans one_pos ht
    have h1 : 0 ≤ 1 - Real.exp (-(a * t)) := by
      have h : Real.exp (-(a * t)) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith [ha, ht0.le])
      simpa using h
    have h2 : 1 - Real.exp (-(a * t)) ≤ 1 := by
      have h := Real.exp_pos (-(a * t)); linarith
    have h3 : 0 ≤ t ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg ht0.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h3)]
    calc (1 - Real.exp (-(a * t))) * t ^ (-(3 : ℝ) / 2)
        ≤ 1 * t ^ (-(3 : ℝ) / 2) := mul_le_mul_of_nonneg_right h2 h3
      _ = t ^ (-(3 : ℝ) / 2) := one_mul _

/-- **Integrability of the subordination kernel.** For `a ≥ 0` the function
`t ↦ (1 − e^{−a t}) t^{−3/2}` is integrable on `(0, ∞)`: on `(0,1]` it is dominated by the
summable `a t^{−1/2}` and on `(1,∞)` by the summable `t^{−3/2}`. -/
theorem subordination_rpow_integrableOn (a : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (fun t : ℝ => (1 - Real.exp (-(a * t))) * t ^ (-(3 : ℝ) / 2))
      (Set.Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  exact (integrableOn_Ioc_one_sub_exp_aux a ha).union (integrableOn_Ioi_one_sub_exp_aux a ha)

end Work.BoseBoxFock.SqrtKin

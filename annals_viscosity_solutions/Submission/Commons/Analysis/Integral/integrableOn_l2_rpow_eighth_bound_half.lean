import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

namespace Commons.Analysis.Integral

open MeasureTheory Set Real

/-- On `(1, √2]`, the base `1 - (1/x)^2` is positive. -/
private lemma one_sub_sq_pos {x : ℝ} (hx : x ∈ Ioc (1:ℝ) (Real.sqrt 2)) :
    0 < 1 - (1 / x) ^ 2 := by
  have hx1 : 1 < x := hx.1
  have hxpos : 0 < x := lt_trans one_pos hx1
  have hx2 : (1:ℝ) < x ^ 2 := by nlinarith
  have hsq : (1 / x) ^ 2 < 1 := by
    rw [div_pow, one_pow, div_lt_one (by positivity : (0:ℝ) < x ^ 2)]
    exact hx2
  linarith

/-- On `(1, √2]`, `x - 1 ≤ 1 - (1/x)^2`. -/
private lemma sub_one_le_one_sub_sq {x : ℝ} (hx : x ∈ Ioc (1:ℝ) (Real.sqrt 2)) :
    x - 1 ≤ 1 - (1 / x) ^ 2 := by
  have hx1 : 1 < x := hx.1
  have hxpos : 0 < x := lt_trans one_pos hx1
  have hxle : x ≤ Real.sqrt 2 := hx.2
  have hx2 : x ^ 2 ≤ 2 := by
    have := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg 2, hxpos, hxle]
  have hx21 : x ^ 2 ≤ x + 1 := by nlinarith
  have hcx : 1 ≤ (x + 1) / x ^ 2 := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < x ^ 2)]
    linarith
  have hu_eq : 1 - (1 / x) ^ 2 = (x - 1) * ((x + 1) / x ^ 2) := by
    field_simp
    ring
  rw [hu_eq]
  calc x - 1 = (x - 1) * 1 := by ring
    _ ≤ (x - 1) * ((x + 1) / x ^ 2) := mul_le_mul_of_nonneg_left hcx (by linarith)

/-- Pointwise domination of the integrand by the `(x-1)^{-1/8}` singularity. -/
private lemma integrand_norm_le {x : ℝ} (hx : x ∈ Ioc (1:ℝ) (Real.sqrt 2)) :
    ‖(1 - (1 / x) ^ 2) ^ (-(1 / 8 : ℝ))
        * Real.sqrt (2 / (1 + Real.sqrt (1 - (1 / x) ^ 2))) * (Real.sqrt x)⁻¹‖
      ≤ Real.sqrt 2 * (x - 1) ^ (-(1 / 8 : ℝ)) := by
  have hx1 : 1 < x := hx.1
  have hxpos : 0 < x := lt_trans one_pos hx1
  have hupos : 0 < 1 - (1 / x) ^ 2 := one_sub_sq_pos hx
  have hxm1 : 0 < x - 1 := by linarith
  -- factor bounds
  have hA : (1 - (1 / x) ^ 2) ^ (-(1 / 8 : ℝ)) ≤ (x - 1) ^ (-(1 / 8 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hxm1 (sub_one_le_one_sub_sq hx) (by norm_num)
  have hden : 0 < 1 + Real.sqrt (1 - (1 / x) ^ 2) := by
    have := Real.sqrt_nonneg (1 - (1 / x) ^ 2); linarith
  have hfrac : 2 / (1 + Real.sqrt (1 - (1 / x) ^ 2)) ≤ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [Real.sqrt_nonneg (1 - (1 / x) ^ 2)]
  have hB : Real.sqrt (2 / (1 + Real.sqrt (1 - (1 / x) ^ 2))) ≤ Real.sqrt 2 :=
    Real.sqrt_le_sqrt hfrac
  have hsx : (1:ℝ) ≤ Real.sqrt x := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (le_of_lt hx1)
  have hC : (Real.sqrt x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsx
  -- nonnegativities
  have hA0 : 0 ≤ (1 - (1 / x) ^ 2) ^ (-(1 / 8 : ℝ)) := Real.rpow_nonneg (le_of_lt hupos) _
  have hB0 : 0 ≤ Real.sqrt (2 / (1 + Real.sqrt (1 - (1 / x) ^ 2))) := Real.sqrt_nonneg _
  have hC0 : 0 ≤ (Real.sqrt x)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg x)
  have hAB0 : 0 ≤ (x - 1) ^ (-(1 / 8 : ℝ)) * Real.sqrt 2 :=
    mul_nonneg (Real.rpow_nonneg (le_of_lt hxm1) _) (Real.sqrt_nonneg 2)
  have hprod : 0 ≤ (1 - (1 / x) ^ 2) ^ (-(1 / 8 : ℝ))
      * Real.sqrt (2 / (1 + Real.sqrt (1 - (1 / x) ^ 2))) * (Real.sqrt x)⁻¹ :=
    mul_nonneg (mul_nonneg hA0 hB0) hC0
  rw [Real.norm_eq_abs, abs_of_nonneg hprod]
  calc (1 - (1 / x) ^ 2) ^ (-(1 / 8 : ℝ))
        * Real.sqrt (2 / (1 + Real.sqrt (1 - (1 / x) ^ 2))) * (Real.sqrt x)⁻¹
      ≤ (x - 1) ^ (-(1 / 8 : ℝ)) * Real.sqrt 2 * 1 :=
        mul_le_mul (mul_le_mul hA hB hB0 (Real.rpow_nonneg (le_of_lt hxm1) _)) hC hC0 hAB0
    _ = Real.sqrt 2 * (x - 1) ^ (-(1 / 8 : ℝ)) := by ring

/-- Continuity of the integrand on `(1, √2]`. -/
private lemma continuousOn_integrand :
    ContinuousOn (fun x : ℝ =>
        (1 - (1 / x) ^ 2) ^ (-(1 / 8 : ℝ))
          * Real.sqrt (2 / (1 + Real.sqrt (1 - (1 / x) ^ 2))) * (Real.sqrt x)⁻¹)
      (Ioc (1:ℝ) (Real.sqrt 2)) := by
  have hdiv : ContinuousOn (fun x : ℝ => 1 / x) (Ioc (1:ℝ) (Real.sqrt 2)) :=
    continuousOn_const.div continuousOn_id (fun x hx => ne_of_gt (lt_trans one_pos hx.1))
  have hu : ContinuousOn (fun x : ℝ => 1 - (1 / x) ^ 2) (Ioc (1:ℝ) (Real.sqrt 2)) :=
    continuousOn_const.sub (hdiv.pow 2)
  have hA : ContinuousOn (fun x : ℝ => (1 - (1 / x) ^ 2) ^ (-(1 / 8 : ℝ)))
      (Ioc (1:ℝ) (Real.sqrt 2)) :=
    hu.rpow_const (fun x hx => Or.inl (ne_of_gt (one_sub_sq_pos hx)))
  have hB : ContinuousOn
      (fun x : ℝ => Real.sqrt (2 / (1 + Real.sqrt (1 - (1 / x) ^ 2))))
      (Ioc (1:ℝ) (Real.sqrt 2)) := by
    have hsqrt : ContinuousOn (fun x : ℝ => Real.sqrt (1 - (1 / x) ^ 2))
        (Ioc (1:ℝ) (Real.sqrt 2)) := hu.sqrt
    have hden : ContinuousOn (fun x : ℝ => 1 + Real.sqrt (1 - (1 / x) ^ 2))
        (Ioc (1:ℝ) (Real.sqrt 2)) := continuousOn_const.add hsqrt
    have hfrac : ContinuousOn (fun x : ℝ => 2 / (1 + Real.sqrt (1 - (1 / x) ^ 2)))
        (Ioc (1:ℝ) (Real.sqrt 2)) :=
      continuousOn_const.div hden (fun x hx => by
        have := Real.sqrt_nonneg (1 - (1 / x) ^ 2); linarith)
    exact hfrac.sqrt
  have hC : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (Ioc (1:ℝ) (Real.sqrt 2)) :=
    continuous_sqrt.continuousOn.inv₀ (fun x hx => ne_of_gt (Real.sqrt_pos.mpr (lt_trans one_pos hx.1)))
  exact (hA.mul hB).mul hC

theorem integrableOn_l2_rpow_eighth_bound_half :
    MeasureTheory.IntegrableOn (fun x : ℝ =>
        (1 - (1 / x) ^ 2) ^ (-(1 / 8 : ℝ)) * Real.sqrt (2 / (1 + Real.sqrt (1 - (1 / x) ^ 2)))
          * (Real.sqrt x)⁻¹)
      (Set.Ioc (1:ℝ) (Real.sqrt 2)) := by
  have hsqrt2_ge1 : (1:ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)
  -- integrability of the model singularity `(x-1)^{-1/8}` on `(1, √2]`
  have hbase : IntegrableOn (fun x : ℝ => (x - 1) ^ (-(1 / 8 : ℝ)))
      (Ioc (1:ℝ) (Real.sqrt 2)) := by
    have hr : IntervalIntegrable (fun y : ℝ => y ^ (-(1 / 8 : ℝ))) volume (0:ℝ) (Real.sqrt 2 - 1) :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have h2 : IntervalIntegrable (fun x : ℝ => (x - 1) ^ (-(1 / 8 : ℝ)))
        volume (1:ℝ) (Real.sqrt 2) := by
      have hc := hr.comp_sub_right (1:ℝ)
      simpa using hc
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hsqrt2_ge1).mp h2
  have hg : IntegrableOn (fun x : ℝ => Real.sqrt 2 * (x - 1) ^ (-(1 / 8 : ℝ)))
      (Ioc (1:ℝ) (Real.sqrt 2)) :=
    hbase.const_mul (Real.sqrt 2)
  refine Integrable.mono' hg ?_ ?_
  · exact continuousOn_integrand.aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact integrand_norm_le hx

end Commons.Analysis.Integral
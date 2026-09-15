import Mathlib
import Submission.Commons.Analysis.Integral.integrable_of_log_le_lorentz

open MeasureTheory Set

namespace Commons.Analysis.Integral

theorem integrable_log_lorentz (a b : ℝ) (ha : 0 < a) :
    MeasureTheory.Integrable (fun t : ℝ => (Real.log (2 + |t|) + 1) / (a ^ 2 + (t - b) ^ 2)) := by
  set M : ℝ := Real.log (3 + |b|) + 3 with hM
  set D : ℝ := M * (min (a^2) 1)⁻¹ with hD
  have hMnn : 0 ≤ M := by
    rw [hM]
    have : 0 ≤ Real.log (3 + |b|) := Real.log_nonneg (by linarith [abs_nonneg b])
    linarith
  have hminpos : 0 < min (a^2) 1 := lt_min (by positivity) one_pos
  have hDnn : 0 ≤ D := by rw [hD]; exact mul_nonneg hMnn (inv_nonneg.mpr hminpos.le)
  have hbase : Integrable (fun t : ℝ => (1 + (t - b) ^ 2) ^ (-((3:ℝ)/4))) volume := by
    have h := (integrable_one_add_sq_rpow_neg ((3:ℝ)/4) (by norm_num)).comp_sub_right b
    simpa using h
  have hdom : Integrable (fun t : ℝ => D * (1 + (t - b) ^ 2) ^ (-((3:ℝ)/4))) volume :=
    hbase.const_mul D
  have hcont : Continuous (fun t : ℝ => (Real.log (2 + |t|) + 1) / (a ^ 2 + (t - b) ^ 2)) := by
    have h1 : ∀ t : ℝ, (2 + |t| : ℝ) ≠ 0 := fun t => by positivity
    have hc1 : Continuous (fun t : ℝ => 2 + |t|) := continuous_const.add continuous_abs
    have hlog : Continuous (fun t : ℝ => Real.log (2 + |t|)) := Continuous.log hc1 h1
    have hnum : Continuous (fun t : ℝ => Real.log (2 + |t|) + 1) := hlog.add continuous_const
    refine hnum.div (by fun_prop) (fun t => ?_)
    have : 0 < a^2 + (t - b)^2 := by positivity
    exact ne_of_gt this
  refine Integrable.mono' hdom hcont.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun t => ?_)
  have hnum0 : 0 ≤ Real.log (2 + |t|) + 1 := by
    have : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
    linarith
  have hdenpos : 0 < a^2 + (t-b)^2 := by positivity
  have hinvnn : 0 ≤ (a^2 + (t-b)^2)⁻¹ := by positivity
  have hlogt : Real.log (2 + |t|) + 1 ≤ M * (1 + (t - b) ^ 2) ^ ((1:ℝ)/4) := by
    rw [hM]; exact log_two_add_abs_le b t
  have hge : min (a^2) 1 * (1 + (t - b) ^ 2) ≤ a^2 + (t - b) ^ 2 := by
    rcases le_total (a^2) 1 with ha1 | ha1
    · rw [min_eq_left ha1]
      nlinarith [sq_nonneg (t-b), mul_le_mul_of_nonneg_right ha1 (sq_nonneg (t-b))]
    · rw [min_eq_right ha1]
      nlinarith [sq_nonneg (t-b)]
  have hinv : (a^2 + (t - b) ^ 2)⁻¹ ≤ (min (a^2) 1)⁻¹ * (1 + (t - b) ^ 2)⁻¹ := by
    have hxpos : 0 < min (a^2) 1 * (1 + (t - b) ^ 2) := mul_pos hminpos (by positivity)
    have h1 := one_div_le_one_div_of_le hxpos hge
    rw [one_div, one_div, mul_inv] at h1
    exact h1
  have hdiv : (1 + (t - b) ^ 2) ^ ((1:ℝ)/4) * (a^2 + (t - b) ^ 2)⁻¹
      ≤ (min (a^2) 1)⁻¹ * (1 + (t - b) ^ 2) ^ (-((3:ℝ)/4)) := by
    calc (1 + (t - b) ^ 2) ^ ((1:ℝ)/4) * (a^2 + (t - b) ^ 2)⁻¹
        ≤ (1 + (t - b) ^ 2) ^ ((1:ℝ)/4)
            * ((min (a^2) 1)⁻¹ * (1 + (t - b) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg (by positivity) _)
      _ = (min (a^2) 1)⁻¹
            * ((1 + (t - b) ^ 2) ^ ((1:ℝ)/4) * (1 + (t - b) ^ 2)⁻¹) := by ring
      _ = (min (a^2) 1)⁻¹ * (1 + (t - b) ^ 2) ^ (-((3:ℝ)/4)) := by
          congr 1
          rw [← Real.rpow_neg_one (1 + (t - b) ^ 2),
              ← Real.rpow_add (by positivity : (0:ℝ) < 1 + (t - b) ^ 2)]
          congr 1; norm_num
  have hfinal : M * ((1 + (t - b) ^ 2) ^ ((1:ℝ)/4) * (a^2 + (t - b) ^ 2)⁻¹)
      ≤ D * (1 + (t - b) ^ 2) ^ (-((3:ℝ)/4)) := by
    rw [hD]
    calc M * ((1 + (t - b) ^ 2) ^ ((1:ℝ)/4) * (a^2 + (t - b) ^ 2)⁻¹)
        ≤ M * ((min (a^2) 1)⁻¹ * (1 + (t - b) ^ 2) ^ (-((3:ℝ)/4))) :=
          mul_le_mul_of_nonneg_left hdiv hMnn
      _ = (M * (min (a^2) 1)⁻¹) * (1 + (t - b) ^ 2) ^ (-((3:ℝ)/4)) := by ring
  have hstep : (Real.log (2 + |t|) + 1) * (a^2 + (t - b) ^ 2)⁻¹
      ≤ D * (1 + (t - b) ^ 2) ^ (-((3:ℝ)/4)) := by
    calc (Real.log (2 + |t|) + 1) * (a^2 + (t - b) ^ 2)⁻¹
        ≤ (M * (1 + (t - b) ^ 2) ^ ((1:ℝ)/4)) * (a^2 + (t - b) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hlogt hinvnn
      _ = M * ((1 + (t - b) ^ 2) ^ ((1:ℝ)/4) * (a^2 + (t - b) ^ 2)⁻¹) := by ring
      _ ≤ D * (1 + (t - b) ^ 2) ^ (-((3:ℝ)/4)) := hfinal
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum0 hdenpos.le), div_eq_mul_inv]
  exact hstep

end Commons.Analysis.Integral

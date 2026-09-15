import Mathlib
import Submission.Commons.Analysis.Integral.gam0_contour_integral_le

open MeasureTheory

namespace Commons.Analysis.Integral

theorem log_pow_div_sq_integrableOn (B c : ℝ) (hB : 0 ≤ B) (hc : 0 < c) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (Real.log (t + 2)) ^ B / (t ^ 2 + c ^ 2)) (Set.Ioi 0) := by
  have hε : 0 < (1:ℝ)/2 := by norm_num
  obtain ⟨Klog, hKlogpos, hKlog⟩ := gam0_log_pow_le_const_mul_rpow B (1/2) hB hε
  set Cden : ℝ := max 2 (8 / c ^ 2) with hCden
  have hCdenpos : 0 < Cden := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hden_le : ∀ t : ℝ, 0 ≤ t → 1 / (t^2 + c^2) ≤ Cden * (t+2)^(-(2:ℝ)) := by
    intro t ht
    have hc2pos : (0:ℝ) < c^2 := by positivity
    have hsq : (t+2)^2 ≤ Cden * (t^2 + c^2) := by
      have h0 : (t + 2)^2 ≤ 2 * t^2 + 8 := by nlinarith [sq_nonneg (t - 2)]
      have ha : 2 * t^2 ≤ Cden * t^2 :=
        mul_le_mul_of_nonneg_right (le_max_left (2:ℝ) (8/c^2)) (sq_nonneg t)
      have hb : (8:ℝ) ≤ Cden * c^2 := by
        have h8le : (8:ℝ) / c^2 ≤ Cden := le_max_right (2:ℝ) (8/c^2)
        have := mul_le_mul_of_nonneg_right h8le (sq_nonneg c)
        rwa [div_mul_cancel₀ 8 (ne_of_gt hc2pos)] at this
      calc (t+2)^2 ≤ 2 * t^2 + 8 := h0
        _ ≤ Cden * t^2 + Cden * c^2 := add_le_add ha hb
        _ = Cden * (t^2 + c^2) := by ring
    have hdenpos : (0:ℝ) < t^2 + c^2 := by positivity
    have h1 : (1:ℝ) / (t^2 + c^2) ≤ Cden / (t+2)^2 := by
      rw [div_le_div_iff₀ hdenpos (by positivity)]
      simpa using hsq
    rw [show Cden * (t + 2) ^ (-(2:ℝ)) = Cden / (t+2)^2 from by
      rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ t+2), Real.rpow_ofNat, div_eq_mul_inv]]
    exact h1
  have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => (t + 2) ^ (-((3:ℝ)/2))) (Set.Ioi 0) :=
    gam0_integrableOn_rpow_shift ((3:ℝ)/2) (by norm_num)
  have hmaj : MeasureTheory.Integrable (fun t : ℝ => Klog * Cden * (t + 2) ^ (-((3:ℝ)/2)))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    simpa using hbase.const_mul (Klog * Cden)
  refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have hlin : ContinuousOn (fun t : ℝ => t + 2) (Set.Ioi 0) :=
      (continuous_id.add continuous_const).continuousOn
    have hlog : ContinuousOn (fun t : ℝ => Real.log (t + 2)) (Set.Ioi 0) :=
      hlin.log (fun t ht => ne_of_gt (by have := Set.mem_Ioi.mp ht; linarith))
    have hlogpos : ∀ t ∈ Set.Ioi (0:ℝ), 0 < Real.log (t + 2) :=
      fun t ht => Real.log_pos (by have := Set.mem_Ioi.mp ht; linarith)
    have hlogpow : ContinuousOn (fun t : ℝ => (Real.log (t + 2)) ^ B) (Set.Ioi 0) :=
      hlog.rpow_const (fun t ht => Or.inl (ne_of_gt (hlogpos t ht)))
    have hden : ContinuousOn (fun t : ℝ => t^2 + c^2) (Set.Ioi 0) :=
      ((continuous_id.pow 2).add continuous_const).continuousOn
    exact hlogpow.div hden (fun t ht => ne_of_gt (by positivity))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hlogpos : 0 < Real.log (t + 2) := Real.log_pos (by linarith)
    have hfnn : 0 ≤ (Real.log (t + 2))^B / (t^2 + c^2) :=
      div_nonneg (Real.rpow_nonneg hlogpos.le B) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
    have hKl : (Real.log (t + 2))^B ≤ Klog * (t + 2)^((1:ℝ)/2) := hKlog (t+2) (by linarith)
    have hdl : 1 / (t^2 + c^2) ≤ Cden * (t+2)^(-(2:ℝ)) := hden_le t (le_of_lt ht0)
    have hXY : (t + 2) ^ ((1:ℝ)/2) * (t + 2) ^ (-(2:ℝ)) = (t + 2) ^ (-((3:ℝ)/2)) := by
      rw [← Real.rpow_add (by linarith : (0:ℝ) < t+2)]
      norm_num
    have hKnn : 0 ≤ Klog := le_of_lt hKlogpos
    have hb1 : 0 ≤ Klog * (t + 2) ^ ((1:ℝ)/2) :=
      mul_nonneg hKnn (Real.rpow_nonneg (by linarith) _)
    calc (Real.log (t + 2))^B / (t^2 + c^2)
        = (Real.log (t + 2))^B * (1 / (t^2 + c^2)) := by rw [div_eq_mul_one_div]
      _ ≤ (Klog * (t + 2)^((1:ℝ)/2)) * (Cden * (t+2)^(-(2:ℝ))) :=
          mul_le_mul hKl hdl (by positivity) hb1
      _ = Klog * Cden * ((t + 2) ^ ((1:ℝ)/2) * (t + 2) ^ (-(2:ℝ))) := by ring
      _ = Klog * Cden * (t + 2) ^ (-((3:ℝ)/2)) := by rw [hXY]

end Commons.Analysis.Integral

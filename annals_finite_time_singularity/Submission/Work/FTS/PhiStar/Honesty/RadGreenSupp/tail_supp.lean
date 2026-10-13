/-
# `Work.FTS.PhiStar.Honesty.RadGreenSupp.tail_supp`

The far-field tail estimate for a function `c` supported in `[a,b] ⊆ (0,∞)`:

  `|∫_{z}^{∞} c t · t^{-p-1} dt| ≤ M · (max z a)^{-p} / p`   (`p > 0`),

where `|c| ≤ M`.  Since `c` vanishes off `[a,b]`, the effective lower limit of integration is
`max z a` (the point `a` itself contributes nothing, being of measure zero), and the primitive
`t^{-p}/p` of `-t^{-p-1}` gives the constant `(max z a)^{-p}/p`.

The proof avoids any measurability hypothesis on `c` by going through the *lower* integral:
`‖∫ f‖ ≤ (∫⁻ ‖f‖).toReal` (`norm_integral_le_lintegral_norm`), and `lintegral` is monotone with
no hypotheses.  The pointwise domination `‖c t · t^{-p-1}‖ ≤ (Ici a).indicator (M t^{-p-1}) t`
holds everywhere (for `t < a` both sides vanish because `c` does), and is integrated against the
measurable weight `M t^{-p-1}` on `(max z a, ∞)`.
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

-- `hab : a ≤ b` is part of the requested statement but the estimate does not use it.
set_option linter.unusedVariables false

namespace Work.FTS.PhiStar.Honesty.RadGreenSupp

theorem tail_supp {c : ℝ → ℝ} {a b M p z : ℝ} (ha : 0 < a) (hab : a ≤ b) (hM : 0 ≤ M)
    (hp : 0 < p) (hsupp : ∀ t : ℝ, t ∉ Set.Icc a b → c t = 0) (hb : ∀ t : ℝ, |c t| ≤ M)
    (hz : 0 < z) :
    |∫ t in Set.Ioi z, c t * t ^ (-p - 1)| ≤ M * (max z a) ^ (-p) / p := by
  have hpm : -p - 1 < -1 := by linarith
  have hc0 : 0 < max z a := lt_of_lt_of_le hz (le_max_left z a)
  set F : ℝ → ℝ := fun t => c t * t ^ (-p - 1) with hF
  have hF0 : ∀ t : ℝ, t ∉ Set.Icc a b → F t = 0 := by
    intro t ht
    simp only [hF]
    rw [hsupp t ht, zero_mul]
  -- pointwise domination of `‖F‖` by the indicator of `M t^{-p-1}` on `Ici a`
  have hpt : ∀ t : ℝ, ENNReal.ofReal ‖F t‖ ≤
      (Set.Ici a).indicator (fun s => ENNReal.ofReal (M * s ^ (-p - 1))) t := by
    intro t
    by_cases hat : a ≤ t
    · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hat)]
      refine ENNReal.ofReal_le_ofReal ?_
      have ht0 : 0 < t := lt_of_lt_of_le ha hat
      rw [hF, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      exact mul_le_mul_of_nonneg_right (hb t) (Real.rpow_nonneg ht0.le _)
    · rw [Set.indicator_of_notMem (fun h => hat (Set.mem_Ici.mp h)), hF0 t (fun hh => hat hh.1),
          norm_zero, ENNReal.ofReal_zero]
  have hk : Measurable (fun s : ℝ => ENNReal.ofReal (M * s ^ (-p - 1))) := by
    apply ENNReal.measurable_ofReal.comp
    exact measurable_const.mul (by measurability)
  -- push the domination into the lower integral on `Ioi z`
  have hB1 : (∫⁻ t in Set.Ioi z, ENNReal.ofReal ‖F t‖) ≤
      ∫⁻ t in Set.Ioi z, (Set.Ici a).indicator (fun s => ENNReal.ofReal (M * s ^ (-p - 1))) t :=
    setLIntegral_mono (hk.indicator measurableSet_Ici) (fun t _ => hpt t)
  -- remove the indicator
  have hB2 : (∫⁻ t in Set.Ioi z,
        (Set.Ici a).indicator (fun s => ENNReal.ofReal (M * s ^ (-p - 1))) t)
      = ∫⁻ t in Set.Ioi z ∩ Set.Ici a, ENNReal.ofReal (M * t ^ (-p - 1)) := by
    rw [lintegral_indicator (μ := volume.restrict (Set.Ioi z)) measurableSet_Ici]
    rw [Measure.restrict_restrict measurableSet_Ici]
    rw [Set.inter_comm]
  -- shrink the region of integration to `Ici (max z a)`
  have hB3 : (∫⁻ t in Set.Ioi z ∩ Set.Ici a, ENNReal.ofReal (M * t ^ (-p - 1)))
      ≤ ∫⁻ t in Set.Ici (max z a), ENNReal.ofReal (M * t ^ (-p - 1)) :=
    lintegral_mono_set (fun t ht => Set.mem_Ici.mpr
      (max_le (le_of_lt (Set.mem_Ioi.mp ht.1)) (Set.mem_Ici.mp ht.2)))
  -- integrability on `Ici (max z a)`
  have hIoi : Integrable (fun t : ℝ => M * t ^ (-p - 1)) (volume.restrict (Set.Ioi (max z a))) :=
    MeasureTheory.Integrable.const_mul (integrableOn_Ioi_rpow_of_lt hpm hc0) M
  have hIci : Integrable (fun t : ℝ => M * t ^ (-p - 1)) (volume.restrict (Set.Ici (max z a))) := by
    simpa [Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := max z a))] using hIoi
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ici (max z a))] (fun t : ℝ => M * t ^ (-p - 1)) :=
    (ae_restrict_mem measurableSet_Ici).mono fun t ht =>
      mul_nonneg hM (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hc0 (Set.mem_Ici.mp ht))) _)
  have hC1 : (∫⁻ t in Set.Ici (max z a), ENNReal.ofReal (M * t ^ (-p - 1)))
      = ENNReal.ofReal (∫ t in Set.Ici (max z a), M * t ^ (-p - 1)) :=
    (ofReal_integral_eq_lintegral_ofReal hIci hnn).symm
  -- the explicit primitive
  have hR : (∫ t in Set.Ici (max z a), M * t ^ (-p - 1)) = M * (max z a) ^ (-p) / p := by
    rw [MeasureTheory.integral_const_mul]
    rw [integral_Ici_eq_integral_Ioi]
    rw [integral_Ioi_rpow_of_lt hpm hc0]
    rw [show (-p - 1 + 1 : ℝ) = -p by ring]
    rw [mul_div_assoc]
    field_simp
  have hsum : (∫⁻ t in Set.Ioi z, ENNReal.ofReal ‖F t‖)
      ≤ ∫⁻ t in Set.Ici (max z a), ENNReal.ofReal (M * t ^ (-p - 1)) :=
    hB1.trans (hB2.trans_le hB3)
  have hmain : ‖∫ t in Set.Ioi z, F t‖ ≤ M * (max z a) ^ (-p) / p := by
    calc ‖∫ t in Set.Ioi z, F t‖
        ≤ (∫⁻ t in Set.Ioi z, ENNReal.ofReal ‖F t‖).toReal :=
          norm_integral_le_lintegral_norm (μ := volume.restrict (Set.Ioi z)) F
      _ ≤ (∫⁻ t in Set.Ici (max z a), ENNReal.ofReal (M * t ^ (-p - 1))).toReal :=
          ENNReal.toReal_mono (by rw [hC1]; exact ENNReal.ofReal_ne_top) hsum
      _ = M * (max z a) ^ (-p) / p := by
          have h0 : 0 ≤ ∫ t in Set.Ici (max z a), M * t ^ (-p - 1) := by
            rw [hR]; positivity
          rw [hC1, ENNReal.toReal_ofReal h0, hR]
  simpa only [hF, Real.norm_eq_abs] using hmain

end Work.FTS.PhiStar.Honesty.RadGreenSupp

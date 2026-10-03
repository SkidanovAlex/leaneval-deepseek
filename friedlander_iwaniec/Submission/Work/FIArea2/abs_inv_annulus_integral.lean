import Mathlib

namespace Work.FIArea2

open MeasureTheory Set intervalIntegral

theorem abs_inv_annulus_integral (s T : ℝ) (hs : 0 < s) (hsT : s ≤ T) :
    ∫ x in Set.Ioo (-T) (-s) ∪ Set.Ioo s T, |x|⁻¹ = 2 * Real.log (T / s) := by
  have hnsT : -T ≤ -s := neg_le_neg hsT
  have h0u : (0 : ℝ) ∉ uIcc s T := by
    rw [uIcc_of_le hsT, mem_Icc]
    exact fun h => absurd h.1 (not_le.mpr hs)
  -- the interval integral over (s, T)
  have hint : ∫ x in s..T, |x|⁻¹ = Real.log (T / s) := by
    have hcongr : ∫ x in s..T, |x|⁻¹ = ∫ x in s..T, x⁻¹ := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hsT, mem_Icc] at hx
      show |x|⁻¹ = x⁻¹
      rw [abs_of_pos (lt_of_lt_of_le hs hx.1)]
    rw [hcongr, integral_inv h0u]
  -- set integral over Ioo s T
  have hright : ∫ x in Set.Ioo s T, |x|⁻¹ = Real.log (T / s) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← integral_of_le hsT]
    exact hint
  -- set integral over Ioo (-T) (-s)
  have hleft : ∫ x in Set.Ioo (-T) (-s), |x|⁻¹ = Real.log (T / s) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← integral_of_le hnsT]
    have habs : ∫ x in (-T)..(-s), |x|⁻¹ = ∫ x in (-T)..(-s), |-x|⁻¹ := by
      apply intervalIntegral.integral_congr
      intro x hx
      show |x|⁻¹ = |-x|⁻¹
      rw [abs_neg]
    have hcomp : ∫ x in (-T)..(-s), |-x|⁻¹ = ∫ x in s..T, |x|⁻¹ := by
      simpa using integral_comp_neg (a := -T) (b := -s) (fun y : ℝ => |y|⁻¹)
    rw [habs, hcomp]
    exact hint
  have hdisj : Disjoint (Set.Ioo (-T) (-s)) (Set.Ioo s T) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [mem_Ioo] at hx1 hx2
    linarith [hx1.2, hx2.1, hs]
  have hcontR : ContinuousOn (fun x : ℝ => |x|⁻¹) (Set.Icc s T) :=
    (continuous_abs.continuousOn (s := Set.Icc s T)).inv₀ (fun x hx => by
      rw [mem_Icc] at hx
      exact abs_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le hs hx.1)))
  have hcontL : ContinuousOn (fun x : ℝ => |x|⁻¹) (Set.Icc (-T) (-s)) :=
    (continuous_abs.continuousOn (s := Set.Icc (-T) (-s))).inv₀ (fun x hx => by
      rw [mem_Icc] at hx
      exact abs_ne_zero.mpr (ne_of_lt (lt_of_le_of_lt hx.2 (neg_lt_zero.mpr hs))))
  have hintR : IntegrableOn (fun x : ℝ => |x|⁻¹) (Set.Ioo s T) :=
    (ContinuousOn.integrableOn_compact isCompact_Icc hcontR).mono_set Ioo_subset_Icc_self
  have hintL : IntegrableOn (fun x : ℝ => |x|⁻¹) (Set.Ioo (-T) (-s)) :=
    (ContinuousOn.integrableOn_compact isCompact_Icc hcontL).mono_set Ioo_subset_Icc_self
  rw [setIntegral_union hdisj measurableSet_Ioo hintL hintR, hleft, hright]
  ring

end Work.FIArea2

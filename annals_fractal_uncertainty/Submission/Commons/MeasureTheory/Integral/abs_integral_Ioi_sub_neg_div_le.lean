import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set
open scoped ENNReal

namespace Commons.MeasureTheory.Integral

theorem abs_integral_Ioi_sub_neg_div_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) {L ρ : ℝ} (hL : 0 ≤ L) (hρ : 0 ≤ ρ)
    (hlip : ∀ a b : E, |g a - g b| ≤ L * ‖a - b‖) (hs : ∀ z : E, ρ < ‖z‖ → g z = 0)
    (x y : E) (hy : ‖y‖ = 1) :
    |∫ t in Set.Ioi (0 : ℝ), (g (x + t • y) - g (x - t • y)) / t| ≤ 2 * L * (ρ + ‖x‖) := by
  let F : ℝ → ℝ := fun t => (g (x + t • y) - g (x - t • y)) / t
  change |∫ t in Set.Ioi (0 : ℝ), F t| ≤ 2 * L * (ρ + ‖x‖)
  have hTnn : (0 : ℝ) ≤ ρ + ‖x‖ := add_nonneg hρ (norm_nonneg x)
  have hdiff : ∀ t : ℝ, x + t • y - (x - t • y) = (2 * t) • y := by
    intro t
    rw [two_mul, add_smul]
    abel
  have hbound : ∀ t : ℝ, ‖F t‖ ≤ 2 * L := by
    intro t
    show ‖(g (x + t • y) - g (x - t • y)) / t‖ ≤ 2 * L
    rcases eq_or_ne t 0 with ht | ht
    · subst ht
      have hz : (g (x + (0:ℝ) • y) - g (x - (0:ℝ) • y)) / (0:ℝ) = 0 := by simp
      rw [hz, norm_zero]
      linarith [hL]
    · have hgt : 0 < |t| := abs_pos.mpr ht
      rw [Real.norm_eq_abs, abs_div]
      have hstep : |g (x + t • y) - g (x - t • y)| ≤ L * (2 * |t|) := by
        have h := hlip (x + t • y) (x - t • y)
        rw [hdiff t, norm_smul, Real.norm_eq_abs, abs_mul,
          abs_of_pos (by norm_num : (0 : ℝ) < 2), hy, mul_one] at h
        exact h
      calc |g (x + t • y) - g (x - t • y)| / |t|
          ≤ (L * (2 * |t|)) / |t| := div_le_div_of_nonneg_right hstep (abs_nonneg t)
        _ = 2 * L := by
            have htne : (|t| : ℝ) ≠ 0 := ne_of_gt hgt
            field_simp
  have hzero : ∀ t : ℝ, ρ + ‖x‖ < t → F t = 0 := by
    intro t ht
    show (g (x + t • y) - g (x - t • y)) / t = 0
    have htpos : 0 < t := by linarith
    have hty : ‖t • y‖ = t := by
      rw [norm_smul, hy, mul_one, Real.norm_eq_abs, abs_of_pos htpos]
    have h1 : ρ < ‖x + t • y‖ := by
      have h := norm_sub_norm_le (t • y) (-x)
      rw [sub_neg_eq_add, norm_neg, hty] at h
      rw [add_comm (t • y) x] at h
      linarith
    have h2 : ρ < ‖x - t • y‖ := by
      have h := norm_sub_norm_le (t • y) x
      rw [hty] at h
      rw [norm_sub_rev] at h
      linarith
    rw [hs (x + t • y) h1, hs (x - t • y) h2]
    simp
  have hrewrite : ∫ t in Set.Ioi (0 : ℝ), F t = ∫ t in Set.Ioc (0 : ℝ) (ρ + ‖x‖), F t := by
    have h1 : ∫ t in Set.Ioi (0 : ℝ), F t
        = ∫ t in Set.Ioi (0 : ℝ), (Set.Ioc (0 : ℝ) (ρ + ‖x‖)).indicator F t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      by_cases hmem : t ∈ Set.Ioc (0 : ℝ) (ρ + ‖x‖)
      · rw [Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem hmem]
        exact hzero t (by
          by_contra h
          exact hmem ⟨ht, le_of_not_gt h⟩)
    have h2 : ∫ t in Set.Ioi (0 : ℝ), (Set.Ioc (0 : ℝ) (ρ + ‖x‖)).indicator F t
        = ∫ t in Set.Ioc (0 : ℝ) (ρ + ‖x‖), F t := by
      have hset : Set.Ioi (0 : ℝ) ∩ Set.Ioc (0 : ℝ) (ρ + ‖x‖) = Set.Ioc (0 : ℝ) (ρ + ‖x‖) := by
        ext t; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]; tauto
      rw [setIntegral_indicator measurableSet_Ioc, hset]
    rw [h1, h2]
  have hmain : ‖∫ t in Set.Ioc (0 : ℝ) (ρ + ‖x‖), F t‖ ≤ 2 * L * (ρ + ‖x‖) := by
    have h1 : ‖∫ t in Set.Ioc (0 : ℝ) (ρ + ‖x‖), F t‖
        ≤ (2 * L) * (volume.restrict (Set.Ioc (0 : ℝ) (ρ + ‖x‖))).real Set.univ := by
      have h := norm_integral_le_of_norm_le_const
        (μ := volume.restrict (Set.Ioc (0 : ℝ) (ρ + ‖x‖))) (f := F) (C := 2 * L)
        (Filter.Eventually.of_forall hbound)
      simpa using h
    have h2 : (volume.restrict (Set.Ioc (0 : ℝ) (ρ + ‖x‖))).real Set.univ = ρ + ‖x‖ := by
      rw [Measure.real_def, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
        ENNReal.toReal_ofReal hTnn]
    rw [h2] at h1
    exact h1
  rw [hrewrite]
  simpa only [Real.norm_eq_abs] using hmain

end Commons.MeasureTheory.Integral
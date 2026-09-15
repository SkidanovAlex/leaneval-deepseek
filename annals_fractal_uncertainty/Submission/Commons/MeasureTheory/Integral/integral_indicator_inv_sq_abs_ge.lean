import Mathlib
import Submission.Commons.MeasureTheory.Integral.integral_Ioi_inv_sq

open MeasureTheory

namespace Commons.MeasureTheory.Integral

theorem integral_indicator_inv_sq_abs_ge {δ : ℝ} (hδ : 0 < δ) :
    (∫ t : ℝ, {t : ℝ | δ ≤ |t|}.indicator (fun t => (t ^ 2)⁻¹) t) = 2 * δ⁻¹ := by
  set F : ℝ → ℝ := fun s => {s : ℝ | δ ≤ s}.indicator (fun s => (s ^ 2)⁻¹) s with hF
  have hF_apply : ∀ s, F s = if δ ≤ s then (s ^ 2)⁻¹ else 0 := by
    intro s
    rw [hF]
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  have h1 : (∫ t : ℝ, {t : ℝ | δ ≤ |t|}.indicator (fun t => (t ^ 2)⁻¹) t)
      = ∫ t : ℝ, F |t| := by
    apply integral_congr_ae
    filter_upwards with t
    rw [hF_apply]
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    by_cases ht : δ ≤ |t|
    · rw [if_pos ht, if_pos ht, sq_abs]
    · rw [if_neg ht, if_neg ht]
  have h2 : ∫ x in Set.Ioi (0 : ℝ), F x = δ⁻¹ := by
    have hcongr : ∫ x in Set.Ioi (0 : ℝ), F x
        = ∫ x in Set.Ioi (0 : ℝ), (Set.Ici δ).indicator (fun x => (x ^ 2)⁻¹) x :=
      setIntegral_congr_fun measurableSet_Ioi (fun x _ => by
        rw [hF_apply]
        by_cases h : δ ≤ x
        · rw [if_pos h, Set.indicator_of_mem (show x ∈ Set.Ici δ from h)]
        · rw [if_neg h, Set.indicator_of_notMem (show x ∉ Set.Ici δ from h)])
    rw [hcongr, setIntegral_indicator measurableSet_Ici]
    have hset : Set.Ioi (0 : ℝ) ∩ Set.Ici δ = Set.Ici δ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
      exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le hδ h, h⟩⟩
    rw [hset, integral_Ici_eq_integral_Ioi, integral_Ioi_inv_sq hδ]
  rw [h1, integral_comp_abs, h2]

end Commons.MeasureTheory.Integral

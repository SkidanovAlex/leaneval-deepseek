import Mathlib
import Submission.Work.LinnikAreas.A5.Weights
import Submission.Work.LinnikAreas.A5.f1_data
import Submission.Work.LinnikAreas.A5.Basic

namespace Work.LinnikAreas.A5

/-- The normalised test function `wc K lam` is globally bounded by `1` and nonnegative.

Both claims are read off the definition: for `t < 0`, `wc = 0`; for `0 ≤ t ≤ K`,
`wc t = sinh((K-t)λ)/sinh(Kλ) ∈ [0,1]`; for `t ≥ K`, `wc t = 0`. -/
theorem wc_bounds (K lam : ℝ) (hK : 0 < K) (hlam : 0 < lam) :
    (∀ t : ℝ, ‖Work.LinnikAreas.A5.wc K lam t‖ ≤ 1) ∧
    (∀ t : ℝ, 0 ≤ Work.LinnikAreas.A5.wc K lam t) := by
  have hsinh_pos : 0 < Real.sinh (K * lam) := Real.sinh_pos_iff.mpr (mul_pos hK hlam)
  have hinv_nonneg : 0 ≤ (Real.sinh (K * lam))⁻¹ := inv_nonneg.mpr hsinh_pos.le
  have hle1 : ∀ t : ℝ, wc K lam t ≤ 1 := by
    intro t
    by_cases ht : 0 ≤ t
    · rw [wc_of_nonneg ht]
      rcases lt_or_ge t K with hKt | hKt
      · rw [f1_of_le hKt.le]
        have hsinh_le : Real.sinh ((K - t) * lam) ≤ Real.sinh (K * lam) :=
          Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_right (by linarith [hKt.le]) hlam.le)
        calc (Real.sinh (K * lam))⁻¹ * Real.sinh ((K - t) * lam)
            ≤ (Real.sinh (K * lam))⁻¹ * Real.sinh (K * lam) :=
              mul_le_mul_of_nonneg_left hsinh_le hinv_nonneg
          _ = 1 := inv_mul_cancel₀ (ne_of_gt hsinh_pos)
      · rw [f1_of_ge hKt, mul_zero]; norm_num
    · rw [wc_of_neg (not_le.mp ht)]; norm_num
  have hnonneg : ∀ t : ℝ, 0 ≤ wc K lam t := by
    intro t
    by_cases ht : 0 ≤ t
    · rw [wc_of_nonneg ht]
      rcases lt_or_ge t K with hKt | hKt
      · rw [f1_of_le hKt.le]
        exact mul_nonneg hinv_nonneg
          (Real.sinh_nonneg_iff.mpr (mul_nonneg (by linarith) hlam.le))
      · rw [f1_of_ge hKt, mul_zero]
    · rw [wc_of_neg (not_le.mp ht)]
  exact ⟨fun t => by rw [Real.norm_of_nonneg (hnonneg t)]; exact hle1 t, hnonneg⟩

end Work.LinnikAreas.A5

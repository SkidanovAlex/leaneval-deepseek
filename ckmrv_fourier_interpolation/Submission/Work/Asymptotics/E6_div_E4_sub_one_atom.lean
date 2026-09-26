import Mathlib
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.E4Fun_sub_one_explicit
import Submission.Work.Kernels.Kernels
import Submission.Work.FunnelNumerics.E4_funnel_bounds

namespace Work.Asymptotics

open UpperHalfPlane

/-!
# `E₆/E₄ - 1 = O(q)` at the cusp

The atom `‖E₆ z / E₄ z - 1‖ ≤ C ‖q(z)‖` for `Im z ≥ 3`, where `q = qParamFun`.

The two level-one Eisenstein series have second-order `q`-expansions at the cusp
(`Work.Asymptotics.E4Fun_two_term`, `Work.Asymptotics.E6Fun_two_term`)

  `E₄ = 1 + 240 q + O(q²)`,   `E₆ = 1 - 504 q + O(q²)`,

so for `Im z ≥ 1`, where `‖q‖ ≤ 1`,

  `E₆ - E₄ = (E₆ - 1) - (E₄ - 1) = O(‖q‖)`,  and  `‖E₄ - 1‖ ≤ (C₄ + 240) ‖q‖ ≤ 1/2`

for `Im z ≥ 3` (the latter because `‖q‖ ≤ e^{-6π} ≪ 1`, quantitatively
`Work.FunnelNumerics.E4_sub_one_le`, which already gives `‖E₄ - 1‖ ≤ 1/2` as soon as
`Im z ≥ 2`).  Hence `‖E₄ z‖ ≥ 1/2` there, and

  `E₆/E₄ - 1 = (E₆ - E₄)/E₄`,  so  `‖E₆/E₄ - 1‖ ≤ 2 ‖E₆ - E₄‖ ≤ 2 (C₄ + C₆ + 744) ‖q‖`. -/

/-- **The atom.**  `‖E₆ z / E₄ z - 1‖ = O(‖q(z)‖)` for `Im z ≥ 3`. -/
theorem E6_div_E4_sub_one_atom :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 3 ≤ z.im →
      ‖Work.Kernels.E6Fun z / Work.Kernels.E4Fun z - 1‖ ≤ C * ‖Work.Kernels.qParamFun z‖ := by
  obtain ⟨C4, hC4pos, hC4⟩ := Work.Asymptotics.E4Fun_two_term
  obtain ⟨C6, hC6pos, hC6⟩ := Work.Asymptotics.E6Fun_two_term
  refine ⟨2 * (C4 + C6 + 744) + 1, by positivity, fun z hz => ?_⟩
  have hz1 : 1 ≤ z.im := by linarith
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := norm_qParamFun_le_one z hz1
  have hq2 : ‖Work.Kernels.qParamFun z‖ ^ 2 ≤ ‖Work.Kernels.qParamFun z‖ := by nlinarith
  -- ## The two first-order bounds
  have hE4d : ‖Work.Kernels.E4Fun z - 1‖ ≤ (C4 + 240) * ‖Work.Kernels.qParamFun z‖ := by
    have h := hC4 z hz1
    have hsplit : Work.Kernels.E4Fun z - 1
        = (Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z)
          + 240 * Work.Kernels.qParamFun z := by ring
    calc ‖Work.Kernels.E4Fun z - 1‖
        = ‖(Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z)
            + 240 * Work.Kernels.qParamFun z‖ := by conv_lhs => rw [hsplit]
      _ ≤ ‖Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z‖
            + ‖(240 : ℂ) * Work.Kernels.qParamFun z‖ := norm_add_le _ _
      _ = ‖Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z‖
            + 240 * ‖Work.Kernels.qParamFun z‖ := by rw [norm_mul]; norm_num
      _ ≤ C4 * ‖Work.Kernels.qParamFun z‖ + 240 * ‖Work.Kernels.qParamFun z‖ := by
            have h2 : C4 * ‖Work.Kernels.qParamFun z‖ ^ 2
                ≤ C4 * ‖Work.Kernels.qParamFun z‖ :=
              mul_le_mul_of_nonneg_left hq2 hC4pos.le
            linarith
      _ = (C4 + 240) * ‖Work.Kernels.qParamFun z‖ := by ring
  have hE6d : ‖Work.Kernels.E6Fun z - 1‖ ≤ (C6 + 504) * ‖Work.Kernels.qParamFun z‖ := by
    have h := hC6 z hz1
    have hsplit : Work.Kernels.E6Fun z - 1
        = (Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z)
          - 504 * Work.Kernels.qParamFun z := by ring
    calc ‖Work.Kernels.E6Fun z - 1‖
        = ‖(Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z)
            - 504 * Work.Kernels.qParamFun z‖ := by conv_lhs => rw [hsplit]
      _ ≤ ‖Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z‖
            + ‖(504 : ℂ) * Work.Kernels.qParamFun z‖ := norm_sub_le _ _
      _ = ‖Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z‖
            + 504 * ‖Work.Kernels.qParamFun z‖ := by rw [norm_mul]; norm_num
      _ ≤ C6 * ‖Work.Kernels.qParamFun z‖ + 504 * ‖Work.Kernels.qParamFun z‖ := by
            have h2 : C6 * ‖Work.Kernels.qParamFun z‖ ^ 2
                ≤ C6 * ‖Work.Kernels.qParamFun z‖ :=
              mul_le_mul_of_nonneg_left hq2 hC6pos.le
            linarith
      _ = (C6 + 504) * ‖Work.Kernels.qParamFun z‖ := by ring
  -- ## `E₄` does not vanish on `{3 ≤ Im z}`
  have hE4low : (1 / 2 : ℝ) ≤ ‖Work.Kernels.E4Fun z‖ :=
    Work.FunnelNumerics.E4_funnel_bounds.2 z hz
  have hE4ne : Work.Kernels.E4Fun z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hE4low
    norm_num at hE4low
  -- ## The difference `E₆ - E₄` is `O(q)`
  have hdiff : ‖Work.Kernels.E6Fun z - Work.Kernels.E4Fun z‖
      ≤ (C4 + C6 + 744) * ‖Work.Kernels.qParamFun z‖ := by
    have hsplit : Work.Kernels.E6Fun z - Work.Kernels.E4Fun z
        = (Work.Kernels.E6Fun z - 1) + (1 - Work.Kernels.E4Fun z) := by ring
    calc ‖Work.Kernels.E6Fun z - Work.Kernels.E4Fun z‖
        = ‖(Work.Kernels.E6Fun z - 1) + (1 - Work.Kernels.E4Fun z)‖ := by rw [hsplit]
      _ ≤ ‖Work.Kernels.E6Fun z - 1‖ + ‖1 - Work.Kernels.E4Fun z‖ := norm_add_le _ _
      _ = ‖Work.Kernels.E6Fun z - 1‖ + ‖Work.Kernels.E4Fun z - 1‖ :=
          by rw [show ‖(1 : ℂ) - Work.Kernels.E4Fun z‖ = ‖Work.Kernels.E4Fun z - 1‖
              from norm_sub_rev 1 (Work.Kernels.E4Fun z)]
      _ ≤ (C6 + 504) * ‖Work.Kernels.qParamFun z‖
            + (C4 + 240) * ‖Work.Kernels.qParamFun z‖ := add_le_add hE6d hE4d
      _ = (C4 + C6 + 744) * ‖Work.Kernels.qParamFun z‖ := by ring
  -- ## Dividing by `E₄`
  have hkey : Work.Kernels.E6Fun z / Work.Kernels.E4Fun z - 1
      = (Work.Kernels.E6Fun z - Work.Kernels.E4Fun z) / Work.Kernels.E4Fun z := by
    exact div_sub_one hE4ne
  calc ‖Work.Kernels.E6Fun z / Work.Kernels.E4Fun z - 1‖
      = ‖(Work.Kernels.E6Fun z - Work.Kernels.E4Fun z) / Work.Kernels.E4Fun z‖ := by rw [hkey]
    _ = ‖Work.Kernels.E6Fun z - Work.Kernels.E4Fun z‖ / ‖Work.Kernels.E4Fun z‖ := norm_div _ _
    _ ≤ ‖Work.Kernels.E6Fun z - Work.Kernels.E4Fun z‖ / (1 / 2) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hE4low
    _ = 2 * ‖Work.Kernels.E6Fun z - Work.Kernels.E4Fun z‖ := by ring
    _ ≤ 2 * ((C4 + C6 + 744) * ‖Work.Kernels.qParamFun z‖) :=
        mul_le_mul_of_nonneg_left hdiff (by norm_num)
    _ ≤ (2 * (C4 + C6 + 744) + 1) * ‖Work.Kernels.qParamFun z‖ := by nlinarith [hq0]

end Work.Asymptotics

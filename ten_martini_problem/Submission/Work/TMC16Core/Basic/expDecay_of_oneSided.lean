import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Basic

theorem expDecay_of_oneSided {u : ℤ → ℂ} {c₁ c₂ C₁ C₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hpos : ∀ k : ℤ, 0 ≤ k → ‖u k‖ ≤ C₁ * Real.exp (-(c₁ * (k : ℝ)))) (hneg : ∀ k : ℤ, k ≤ 0 → ‖u k‖ ≤ C₂ * Real.exp (-(c₂ * |(k : ℝ)|))) : Work.TMC16Core.ExpDecay u := by
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, max (max C₁ C₂) 0, ?_⟩
  have hcle₁ : min c₁ c₂ ≤ c₁ := min_le_left _ _
  have hcle₂ : min c₁ c₂ ≤ c₂ := min_le_right _ _
  have hC₁ : C₁ ≤ max (max C₁ C₂) 0 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC₂ : C₂ ≤ max (max C₁ C₂) 0 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hC0 : (0 : ℝ) ≤ max (max C₁ C₂) 0 := le_max_right _ _
  intro k
  by_cases hk : 0 ≤ k
  · have hkR : (0 : ℝ) ≤ (k : ℝ) := Int.cast_nonneg hk
    have habs : |(k : ℝ)| = (k : ℝ) := abs_of_nonneg hkR
    rw [habs]
    have hm : -(c₁ * (k : ℝ)) ≤ -(min c₁ c₂ * (k : ℝ)) := by
      have h : min c₁ c₂ * (k : ℝ) ≤ c₁ * (k : ℝ) := mul_le_mul_of_nonneg_right hcle₁ hkR
      linarith
    have he : Real.exp (-(c₁ * (k : ℝ))) ≤ Real.exp (-(min c₁ c₂ * (k : ℝ))) :=
      Real.exp_le_exp.mpr hm
    refine le_trans (hpos k hk) ?_
    by_cases hC₁0 : 0 ≤ C₁
    · exact le_trans (mul_le_mul_of_nonneg_left he hC₁0)
        (mul_le_mul_of_nonneg_right hC₁ (Real.exp_nonneg _))
    · have h1 : C₁ * Real.exp (-(c₁ * (k : ℝ))) < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hC₁0) (Real.exp_pos _)
      exact le_trans (le_of_lt h1) (mul_nonneg hC0 (Real.exp_nonneg _))
  · have hk_le : k ≤ 0 := le_of_lt (lt_of_not_ge hk)
    have hkabs : (0 : ℝ) ≤ |(k : ℝ)| := abs_nonneg _
    have hm : -(c₂ * |(k : ℝ)|) ≤ -(min c₁ c₂ * |(k : ℝ)|) := by
      have h : min c₁ c₂ * |(k : ℝ)| ≤ c₂ * |(k : ℝ)| := mul_le_mul_of_nonneg_right hcle₂ hkabs
      linarith
    have he : Real.exp (-(c₂ * |(k : ℝ)|)) ≤ Real.exp (-(min c₁ c₂ * |(k : ℝ)|)) :=
      Real.exp_le_exp.mpr hm
    refine le_trans (hneg k hk_le) ?_
    by_cases hC₂0 : 0 ≤ C₂
    · exact le_trans (mul_le_mul_of_nonneg_left he hC₂0)
        (mul_le_mul_of_nonneg_right hC₂ (Real.exp_nonneg _))
    · have h1 : C₂ * Real.exp (-(c₂ * |(k : ℝ)|)) < 0 :=
        mul_neg_of_neg_of_pos (lt_of_not_ge hC₂0) (Real.exp_pos _)
      exact le_trans (le_of_lt h1) (mul_nonneg hC0 (Real.exp_nonneg _))

end Work.TMC16Core.Basic

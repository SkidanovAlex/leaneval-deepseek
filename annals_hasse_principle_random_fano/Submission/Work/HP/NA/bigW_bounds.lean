import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.bigW_le_pow

set_option autoImplicit false

open Filter

namespace Work.HP.NA

theorem bigW_bounds (φ : ℝ) (hφ : 1 < φ) :
    ∀ᶠ A in atTop, (1 : ℝ) ≤ (Work.HP.bigW (Work.HP.wOf (A * φ)) : ℝ) ∧
      (Work.HP.bigW (Work.HP.wOf (A * φ)) : ℝ) ≤ A := by
  obtain ⟨B₀, hB₀⟩ := Work.HP.bigW_le_pow (1 / 2) (by norm_num)
  filter_upwards [eventually_ge_atTop (max B₀ φ), eventually_ge_atTop φ] with A hA hAφ
  have hφpos : 0 < φ := by linarith
  have hApos : 0 < A := lt_of_lt_of_le hφpos hAφ
  have hB₀le : B₀ ≤ A * φ := by
    have h1 : A ≤ A * φ := by
      calc A = A * 1 := (mul_one A).symm
        _ ≤ A * φ := mul_le_mul_of_nonneg_left (le_of_lt hφ) (le_of_lt hApos)
    exact le_trans (le_trans (le_max_left B₀ φ) hA) h1
  refine ⟨?_, ?_⟩
  · exact_mod_cast Work.HP.one_le_bigW (Work.HP.wOf (A * φ))
  · have hWle : (Work.HP.bigW (Work.HP.wOf (A * φ)) : ℝ) ≤ (A * φ) ^ (1 / 2 : ℝ) :=
      hB₀ (A * φ) hB₀le
    refine le_trans hWle ?_
    rw [← Real.sqrt_eq_rpow]
    rw [Real.sqrt_le_left (le_of_lt hApos)]
    nlinarith [hAφ, hApos]

end Work.HP.NA

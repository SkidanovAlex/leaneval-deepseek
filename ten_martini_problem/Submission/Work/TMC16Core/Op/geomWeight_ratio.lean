import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Op

/-- For a nonnegative integer `k`, `(k+1).natAbs = k.natAbs + 1`. -/
private lemma geom_natAbs_add_one (k : ℤ) (h : 0 ≤ k) : (k + 1).natAbs = k.natAbs + 1 := by
  rw [Int.natAbs_eq_iff]
  left
  push_cast
  rw [abs_of_nonneg h]

/-- For a negative integer `k`, `k.natAbs = (k+1).natAbs + 1`. -/
private lemma geom_natAbs_eq_succ (k : ℤ) (h : k < 0) : k.natAbs = (k + 1).natAbs + 1 := by
  rw [Int.natAbs_eq_iff]
  right
  push_cast
  rw [abs_of_nonpos (show k + 1 ≤ 0 by omega)]
  ring

/-- The key ratio identity: `ρ^{|k|} / ρ^{|k+1|}` equals `ρ⁻¹` for `k ≥ 0` and `ρ` for `k < 0`. -/
private lemma geom_pow_ratio (ρ : ℝ) (hρ0 : 0 < ρ) (k : ℤ) :
    ρ ^ k.natAbs / ρ ^ (k + 1).natAbs = if 0 ≤ k then ρ⁻¹ else ρ := by
  by_cases hk : 0 ≤ k
  · rw [if_pos hk, geom_natAbs_add_one k hk, pow_succ]
    field_simp
  · rw [if_neg hk]
    have hk' : k < 0 := by omega
    rw [geom_natAbs_eq_succ k hk', pow_succ]
    field_simp

/-- `|ρ⁻¹ - 1| = (1-ρ)/ρ` exactly, for `0 < ρ ≤ 1`. -/
private lemma geom_abs_inv_sub_one_le (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    |σ⁻¹ - 1| ≤ (1 - σ) / σ := by
  have h1 : σ⁻¹ - 1 = (1 - σ) / σ := by field_simp
  rw [h1, abs_of_nonneg (div_nonneg (by linarith) (le_of_lt hσ0))]

/-- `|ρ - 1| ≤ (1-ρ)/ρ`, for `0 < ρ ≤ 1`. -/
private lemma geom_abs_sub_one_le (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    |σ - 1| ≤ (1 - σ) / σ := by
  rw [abs_of_nonpos (by linarith : σ - 1 ≤ 0)]
  have h : (1 - σ) / σ - (1 - σ) = (1 - σ) ^ 2 / σ := by field_simp
  have hnn : 0 ≤ (1 - σ) ^ 2 / σ := div_nonneg (sq_nonneg _) (le_of_lt hσ0)
  linarith

theorem geomWeight_ratio {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (n₀ n : ℤ) :
    |ρ ^ ((n - n₀).natAbs) / ρ ^ ((n + 1 - n₀).natAbs) - 1| ≤ (1 - ρ) / ρ ∧
      |ρ ^ ((n - n₀).natAbs) / ρ ^ ((n - 1 - n₀).natAbs) - 1| ≤ (1 - ρ) / ρ := by
  set k : ℤ := n - n₀ with hk
  have h₁ : n + 1 - n₀ = k + 1 := by omega
  have h₂ : n - 1 - n₀ = k - 1 := by omega
  rw [h₁, h₂]
  constructor
  · rw [geom_pow_ratio ρ hρ0 k]
    by_cases hk0 : 0 ≤ k
    · rw [if_pos hk0]; exact geom_abs_inv_sub_one_le ρ hρ0 hρ1
    · rw [if_neg hk0]; exact geom_abs_sub_one_le ρ hρ0 hρ1
  · have hkn : k.natAbs = (-k).natAbs := by rw [Int.natAbs_neg]
    have hkc : (k - 1).natAbs = ((-k) + 1).natAbs := by
      have : k - 1 = -((-k) + 1) := by ring
      rw [this, Int.natAbs_neg]
    rw [hkn, hkc, geom_pow_ratio ρ hρ0 (-k)]
    by_cases hk0 : 0 ≤ -k
    · rw [if_pos hk0]; exact geom_abs_inv_sub_one_le ρ hρ0 hρ1
    · rw [if_neg hk0]; exact geom_abs_sub_one_le ρ hρ0 hρ1

end Work.TMC16Core.Op

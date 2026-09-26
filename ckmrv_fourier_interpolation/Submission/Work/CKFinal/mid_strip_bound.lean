import Mathlib

namespace Work.CKFinal

/-- Auxiliary: for `0 < y`, `y ≤ 2` and `0 ≤ β`, we have `2 ^ β * y ^ (-β) ≥ 1`. -/
private lemma one_le_rpow_mul (y β : ℝ) (hy : 0 < y) (hy2 : y ≤ 2) (hβ : 0 ≤ β) :
    1 ≤ 2 ^ β * y ^ (-β) := by
  have hy0 : 0 ≤ y := le_of_lt hy
  have hyβ : y ^ β ≤ 2 ^ β := Real.rpow_le_rpow hy0 hy2 hβ
  have hynβ : 0 ≤ y ^ (-β) := Real.rpow_nonneg hy0 _
  have h1 : y ^ β * y ^ (-β) = 1 := by
    rw [← Real.rpow_add hy β (-β)]; norm_num
  rw [← h1]
  exact mul_le_mul_of_nonneg_right hyβ hynβ

/-- Auxiliary: for `0 < y`, `y ≤ 2` and `0 ≤ β₀ ≤ β`, we have `y ^ (-β₀) ≤ 2 ^ β * y ^ (-β)`. -/
private lemma rpow_neg_le (y β β₀ : ℝ) (hy : 0 < y) (hy2 : y ≤ 2) (hβ₀ : 0 ≤ β₀) (hβ : β₀ ≤ β) :
    y ^ (-β₀) ≤ 2 ^ β * y ^ (-β) := by
  have hy0 : 0 ≤ y := le_of_lt hy
  have hynβ : 0 ≤ y ^ (-β) := Real.rpow_nonneg hy0 _
  have hle : y ^ (β - β₀) ≤ 2 ^ β := by
    have h1 : y ^ (β - β₀) ≤ (2:ℝ) ^ (β - β₀) := Real.rpow_le_rpow hy0 hy2 (sub_nonneg.mpr hβ)
    have h2 : (2:ℝ) ^ (β - β₀) ≤ (2:ℝ) ^ β :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    linarith
  have heq : y ^ (-β₀) = y ^ (β - β₀) * y ^ (-β) := by
    have hae : (β - β₀) + (-β) = -β₀ := by ring
    calc y ^ (-β₀) = y ^ ((β - β₀) + (-β)) := by rw [hae]
      _ = y ^ (β - β₀) * y ^ (-β) := Real.rpow_add hy (β - β₀) (-β)
  rw [heq]
  exact mul_le_mul_of_nonneg_right hle hynβ

theorem mid_strip_bound (α₀ β₀ γ₀ δ₀ β : ℝ) (hα₀ : 0 ≤ α₀) (hβ₀ : 0 ≤ β₀) (hγ₀ : 0 ≤ γ₀)
    (hδ₀ : 0 ≤ δ₀) (hβ : β₀ ≤ β) :
    ∀ y : ℝ, 0 < y → y ≤ 2 →
      α₀ * y ^ (-β₀) + γ₀ * 3 ^ δ₀ ≤ ((α₀ + γ₀ * 3 ^ δ₀) * 2 ^ β) * y ^ (-β) := by
  intro y hy hy2
  have hβ0 : 0 ≤ β := le_trans hβ₀ hβ
  have h3pos : (0:ℝ) < 3 ^ δ₀ := Real.rpow_pos_of_pos (by norm_num) δ₀
  have hC : 0 ≤ γ₀ * 3 ^ δ₀ := mul_nonneg hγ₀ h3pos.le
  have key1 : 1 ≤ 2 ^ β * y ^ (-β) := one_le_rpow_mul y β hy hy2 hβ0
  have key2 : y ^ (-β₀) ≤ 2 ^ β * y ^ (-β) := rpow_neg_le y β β₀ hy hy2 hβ₀ hβ
  calc α₀ * y ^ (-β₀) + γ₀ * 3 ^ δ₀
      ≤ α₀ * (2 ^ β * y ^ (-β)) + (γ₀ * 3 ^ δ₀) * (2 ^ β * y ^ (-β)) :=
        add_le_add (mul_le_mul_of_nonneg_left key2 hα₀)
          (by have := mul_le_mul_of_nonneg_left key1 hC; simpa using this)
    _ = ((α₀ + γ₀ * 3 ^ δ₀) * 2 ^ β) * y ^ (-β) := by ring

end Work.CKFinal

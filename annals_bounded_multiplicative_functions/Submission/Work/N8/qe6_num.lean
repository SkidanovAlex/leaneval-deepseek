import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

theorem qe6_num (ℓ : ℕ) (ε X P₁ P₂ : ℝ) (hε : 0 < ε) (hX1 : 1 ≤ X)
    (hlog1 : 1 ≤ Real.log X)
    (hP1l : X ^ (ε ^ 2 / 2) ≤ P₁) (hP1u : P₁ ≤ X ^ ε)
    (hP2l : X ^ (ε ^ 2 / 2) ≤ P₂) (hrpow4 : 4 ≤ X ^ (ε ^ 2 / 2)) :
    (2 * (ℓ : ℝ) + 2) * Real.log (2 * P₁) + Real.log (X / (P₁ * P₂)) + 1
      ≤ ((2 * (ℓ : ℝ) + 2) * (ε + Real.log 2) + 2) * Real.log X := by
  have hX0 : 0 < X := by linarith
  have hXa_pos : 0 < X ^ (ε ^ 2 / 2) := Real.rpow_pos_of_pos hX0 _
  have hP1_pos : 0 < P₁ := lt_of_lt_of_le hXa_pos hP1l
  have hP2_pos : 0 < P₂ := lt_of_lt_of_le hXa_pos hP2l
  have hP1_ne : P₁ ≠ 0 := ne_of_gt hP1_pos
  have hP2_ne : P₂ ≠ 0 := ne_of_gt hP2_pos
  have hX_ne : X ≠ 0 := ne_of_gt hX0
  have hlog2P1 : Real.log (2 * P₁) ≤ Real.log 2 + ε * Real.log X := by
    rw [Real.log_mul (by norm_num) hP1_ne]
    have : Real.log P₁ ≤ ε * Real.log X := by
      have h := Real.log_le_log hP1_pos hP1u
      rwa [Real.log_rpow hX0] at h
    linarith
  have hlogdiv : Real.log (X / (P₁ * P₂)) ≤ Real.log X - ε ^ 2 * Real.log X := by
    rw [Real.log_div hX_ne (by positivity)]
    have h1 : (ε ^ 2 / 2) * Real.log X ≤ Real.log P₁ := by
      have h := Real.log_le_log hXa_pos hP1l
      rwa [Real.log_rpow hX0] at h
    have h2 : (ε ^ 2 / 2) * Real.log X ≤ Real.log P₂ := by
      have h := Real.log_le_log hXa_pos hP2l
      rwa [Real.log_rpow hX0] at h
    rw [Real.log_mul hP1_ne hP2_ne]
    linarith
  have hc : 0 ≤ 2 * (ℓ : ℝ) + 2 := by positivity
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [hlog2P1, hlogdiv, hc, hl, hlog1, sq_nonneg ε,
    mul_nonneg hc (sub_nonneg.mpr hlog1),
    mul_nonneg (mul_nonneg hc hl) (sub_nonneg.mpr hlog1),
    mul_nonneg (sq_nonneg ε) (by linarith : (0 : ℝ) ≤ Real.log X),
    mul_nonneg hc (by linarith : (0 : ℝ) ≤ Real.log X)]

end Work.N8

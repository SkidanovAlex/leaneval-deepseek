import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mrlas

/-- Arithmetic core of the `log 2` normalisation: `2 * 2^(-(1+α)) = 2^(-α)`. -/
private lemma two_mul_rpow_neg_one_add (α : ℝ) :
    2 * (2 : ℝ) ^ (-(1 + α)) = (2 : ℝ) ^ (-α) := by
  calc 2 * (2 : ℝ) ^ (-(1 + α)) = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-(1 + α)) := by
        rw [Real.rpow_one]
    _ = (2 : ℝ) ^ ((1 : ℝ) + -(1 + α)) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ = (2 : ℝ) ^ (-α) := by congr 1; ring

lemma resonance_arith (C1 : ℝ) (hC1 : 0 ≤ C1) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (1 / Real.log 2) * (C1 / (1 - 2 * (2 : ℝ) ^ (-(1 + α)))) ≤ (4 * C1 / Real.log 2) / α := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [two_mul_rpow_neg_one_add]
  -- `1 - 2^(-α)` is strictly positive.
  have hDpos : 0 < 1 - (2 : ℝ) ^ (-α) := by
    have := Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (z := -α) (by norm_num) (by linarith)
    linarith
  -- Rewrite `2^(-α)` as `(1/2)^α` to apply Bernoulli's inequality.
  have hhalf : ((1 : ℝ) / 2) ^ α = (2 : ℝ) ^ (-α) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
    simp [one_div]
  -- Bernoulli: `(1 - 1/2)^α ≤ 1 - α/2`, i.e. `2^(-α) ≤ 1 - α/2`.
  have hbern : (2 : ℝ) ^ (-α) ≤ 1 - α / 2 := by
    have h := rpow_one_add_le_one_add_mul_self (s := (-(1 / 2) : ℝ)) (p := α)
      (by norm_num) hα0.le hα1
    rw [show (1 : ℝ) + -(1 / 2) = 1 / 2 by norm_num] at h
    calc (2 : ℝ) ^ (-α) = ((1 : ℝ) / 2) ^ α := hhalf.symm
      _ ≤ 1 + α * (-(1 / 2)) := h
      _ = 1 - α / 2 := by ring
  have hD4 : α ≤ 4 * (1 - (2 : ℝ) ^ (-α)) := by linarith
  have hCkey : C1 / (1 - (2 : ℝ) ^ (-α)) ≤ 4 * C1 / α := by
    rw [div_le_div_iff₀ hDpos hα0]
    nlinarith [mul_le_mul_of_nonneg_left hD4 hC1]
  calc (1 / Real.log 2) * (C1 / (1 - (2 : ℝ) ^ (-α)))
      ≤ (1 / Real.log 2) * (4 * C1 / α) := by
        exact mul_le_mul_of_nonneg_left hCkey (by positivity)
    _ = (4 * C1 / Real.log 2) / α := by field_simp

end Work.BMF.mrlas

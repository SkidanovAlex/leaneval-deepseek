import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_core

theorem exists_C_recip_sqrt (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 12 ≤ C ∧ 2 / Real.sqrt C ≤ δ := by
  refine ⟨max 12 ((2 / δ) ^ 2 + 1), le_max_left _ _, ?_⟩
  have hδne : δ ≠ 0 := ne_of_gt hδ
  have hle : (2 / δ) ^ 2 ≤ max 12 ((2 / δ) ^ 2 + 1) :=
    le_trans (le_add_of_nonneg_right zero_le_one) (le_max_right _ _)
  have hsqrt_ge : 2 / δ ≤ Real.sqrt (max 12 ((2 / δ) ^ 2 + 1)) :=
    Real.le_sqrt_of_sq_le hle
  have hsqrtpos : 0 < Real.sqrt (max 12 ((2 / δ) ^ 2 + 1)) :=
    lt_of_lt_of_le (div_pos two_pos hδ) hsqrt_ge
  rw [div_le_iff₀ hsqrtpos]
  calc (2 : ℝ) = δ * (2 / δ) := by rw [mul_comm, div_mul_cancel₀ 2 hδne]
    _ ≤ δ * Real.sqrt (max 12 ((2 / δ) ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left hsqrt_ge hδ.le

end Work.BMF.mr_core

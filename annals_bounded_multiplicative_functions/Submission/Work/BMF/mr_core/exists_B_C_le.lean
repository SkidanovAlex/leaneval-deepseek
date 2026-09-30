import Mathlib
import Submission.Work.BMF.mr_core.exists_B_tail
import Submission.Work.BMF.mr_core.exists_C_recip_sqrt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Choosing the parameters `B` and `C`

The tail factor `(1 + B²/2) e^{-B²/2}` and the "reciprocal square-root" factor
`2 / √C` can both be made smaller than any prescribed positive quantity `δ` by
choosing `B` (resp. `C`) large enough while keeping `B ≥ 8` (resp. `C ≥ 12`).

Combining the two with the prescribed budget `δ = √(ε/384) / (18 Ch)` yields,
for every `Ch > 0` and `ε > 0`, parameters `B ≥ 8`, `C ≥ 12` with
`9 Ch ((1 + B²/2) e^{-B²/2} + 2/√C) ≤ √(ε/384)`.
-/

namespace Work.BMF.mr_core

theorem exists_B_C_le (Ch ε : ℝ) (hCh : 0 < Ch) (hε : 0 < ε) :
    ∃ B C : ℝ, 8 ≤ B ∧ 12 ≤ C ∧
      9 * Ch * ((1 + B ^ 2 / 2) * Real.exp (-(B ^ 2 / 2)) + 2 / Real.sqrt C)
        ≤ Real.sqrt (ε / 384) := by
  set δ : ℝ := Real.sqrt (ε / 384) / (18 * Ch) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  obtain ⟨B, hB8, hBle⟩ := exists_B_tail δ hδpos
  obtain ⟨C, hC12, hCle⟩ := exists_C_recip_sqrt δ hδpos
  refine ⟨B, C, hB8, hC12, ?_⟩
  have hCh9 : (0 : ℝ) ≤ 9 * Ch := by positivity
  calc 9 * Ch * ((1 + B ^ 2 / 2) * Real.exp (-(B ^ 2 / 2)) + 2 / Real.sqrt C)
      ≤ 9 * Ch * (δ + δ) :=
        mul_le_mul_of_nonneg_left (add_le_add hBle hCle) hCh9
    _ = 18 * Ch * δ := by ring
    _ = Real.sqrt (ε / 384) := by rw [hδ]; field_simp

end Work.BMF.mr_core

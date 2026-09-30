import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

theorem qe6_den (ε X P₂ : ℝ) (hε : 0 < ε) (hX : 0 < X)
    (hlog2 : 4 * Real.log 2 / ε ^ 2 ≤ Real.log X)
    (hP2l : X ^ (ε ^ 2 / 2) ≤ P₂) (hrpow4 : 4 ≤ X ^ (ε ^ 2 / 2)) :
    ε ^ 2 / 4 * Real.log X ≤ Real.log (P₂ / 2) := by
  have hε2pos : 0 < ε ^ 2 := pow_pos hε 2
  have hrpow_pos : 0 < X ^ (ε ^ 2 / 2) := Real.rpow_pos_of_pos hX _
  -- monotonicity of log on the (positive) argument
  have hlog_le : Real.log (X ^ (ε ^ 2 / 2) / 2) ≤ Real.log (P₂ / 2) := by
    apply Real.log_le_log
    · positivity
    · linarith
  have hlog_expr : Real.log (X ^ (ε ^ 2 / 2) / 2) = ε ^ 2 / 2 * Real.log X - Real.log 2 := by
    rw [Real.log_div (ne_of_gt hrpow_pos) (by norm_num : (2:ℝ) ≠ 0),
        Real.log_rpow hX]
  have hkey : 4 * Real.log 2 ≤ ε ^ 2 * Real.log X := by
    have := (div_le_iff₀ hε2pos).mp hlog2
    linarith
  have harith : ε ^ 2 / 4 * Real.log X ≤ ε ^ 2 / 2 * Real.log X - Real.log 2 := by
    nlinarith [hkey]
  calc
    ε ^ 2 / 4 * Real.log X ≤ ε ^ 2 / 2 * Real.log X - Real.log 2 := harith
    _ = Real.log (X ^ (ε ^ 2 / 2) / 2) := hlog_expr.symm
    _ ≤ Real.log (P₂ / 2) := hlog_le

end Work.N8

import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

theorem qe6_pi0_lower (ε X P₂ : ℝ) (hε : 0 < ε) (hX : 0 < X) (hlog1 : 1 ≤ Real.log X)
    (hP2l : X ^ (ε ^ 2 / 2) ≤ P₂) (hP2u : P₂ ≤ X ^ ε)
    (hrpow4 : 4 ≤ X ^ (ε ^ 2 / 2)) :
    X ^ (ε ^ 2 / 2) / (ε * Real.log X) ≤ Work.BMF.pi0 P₂ := by
  have hApos : 0 < X ^ (ε ^ 2 / 2) := Real.rpow_pos_of_pos hX _
  have hA1 : 1 < X ^ (ε ^ 2 / 2) := lt_of_lt_of_le (by norm_num) hrpow4
  have hlogApos : 0 < Real.log (X ^ (ε ^ 2 / 2)) := Real.log_pos hA1
  have hPpos : 0 < P₂ := lt_of_lt_of_le hApos hP2l
  have hlogPpos : 0 < Real.log P₂ :=
    lt_of_lt_of_le hlogApos (Real.log_le_log hApos hP2l)
  have hlogPle : Real.log P₂ ≤ ε * Real.log X := by
    have h := Real.log_le_log hPpos hP2u
    rwa [Real.log_rpow hX ε] at h
  rw [Work.BMF.pi0]
  exact div_le_div₀ (le_of_lt hPpos) hP2l hlogPpos hlogPle

end Work.N8

import Mathlib
import Submission.Work.BMF.mr_direct.range_defs
import Submission.Work.BMF.mr_direct.goodSet_E1_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- `∑_{m ∈ winIdxR K A B j} 1/m² ≤ 2 e^{(j+1)/K}/A`. -/
lemma winIdxR_inv_sq_le (K A B : ℝ) (j : ℕ) (hA : 0 < A) :
    ∑ m ∈ Work.BMF.mrDirect.winIdxR K A B j, (1 : ℝ) / (m : ℝ) ^ 2
      ≤ 2 * Real.exp (((j : ℝ) + 1) / K) / A := by
  -- `winIdxR K A B j = ℕ ∩ [A e^{-(j+1)/K}, B e^{-j/K}]`; the elementary window bound
  -- `natIcc_inv_sq_sum_le` with lower end `A e^{-(j+1)/K}` gives `2 / (A e^{-(j+1)/K})`,
  -- and `2 / (A e^{-(j+1)/K}) = 2 e^{(j+1)/K}/A`.
  have hA' : 0 < A * Real.exp (-((j : ℝ) + 1) / K) := mul_pos hA (Real.exp_pos _)
  have h := natIcc_inv_sq_sum_le (A * Real.exp (-((j : ℝ) + 1) / K))
      (B * Real.exp (-(j : ℝ) / K)) hA'
  have heq : 2 / (A * Real.exp (-((j : ℝ) + 1) / K))
      = 2 * Real.exp (((j : ℝ) + 1) / K) / A := by
    rw [show -((j : ℝ) + 1) / K = -(((j : ℝ) + 1) / K) by ring]
    rw [Real.exp_neg]
    field_simp
  rw [heq] at h
  exact h

end Work.BMF.mr_direct

import Mathlib
import Submission.Work.BMF.mr_direct.range_defs
import Submission.Work.BMF.mr_direct.sum_inv_sq_filter_dvd_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- `∑_{m ∈ winIdxR K A B j, p ∣ m} 1/m² ≤ 2 e^{(j+1)/K}/(p·A)`. -/
lemma winIdxR_filter_dvd_inv_sq_le (K A B : ℝ) (j : ℕ) (p : ℕ) (hA : 0 < A) (hp : 1 ≤ p) :
    ∑ m ∈ (Work.BMF.mrDirect.winIdxR K A B j).filter (fun m => p ∣ m),
        (1 : ℝ) / (m : ℝ) ^ 2
      ≤ 2 * Real.exp (((j : ℝ) + 1) / K) / ((p : ℝ) * A) := by
  -- `winIdxR K A B j = natIcc (A e^{-(j+1)/K}) (B e^{-j/K})`, so every `m` in the window
  -- satisfies `m ≥ A e^{-(j+1)/K}`; the multiples of `p` among them are then bounded by the
  -- telescoping estimate `sum_inv_sq_filter_dvd_le`.
  have hM : 0 < A * Real.exp (-((j : ℝ) + 1) / K) := mul_pos hA (Real.exp_pos _)
  have h := sum_inv_sq_filter_dvd_le (A * Real.exp (-((j : ℝ) + 1) / K))
    (B * Real.exp (-(j : ℝ) / K)) p hM hp
  rw [Work.BMF.mrDirect.winIdxR]
  refine h.trans ?_
  -- `2/(p · A e^{-(j+1)/K}) = 2 e^{(j+1)/K}/(p · A)`.
  have hE : Real.exp (-((j : ℝ) + 1) / K) = (Real.exp (((j : ℝ) + 1) / K))⁻¹ := by
    rw [show -((j : ℝ) + 1) / K = -(((j : ℝ) + 1) / K) by ring, Real.exp_neg]
  rw [hE]
  field_simp
  norm_num

end Work.BMF.mr_direct

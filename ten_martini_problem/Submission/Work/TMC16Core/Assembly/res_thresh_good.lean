import Mathlib

namespace Work.TMC16Core.Assembly

/-- Threshold existence: since `εf > 0`, the affine-in-`qn` right-hand side
`L + (19/8)*εf*qn + εf` eventually dominates the constant `Real.log 2`. -/
theorem res_thresh_good {L εf : ℝ} (hL : 0 < L) (hεf : 0 < εf) :
    ∃ Q : ℕ, ∀ qn : ℕ, Q ≤ qn → Real.log 2 ≤ L + (19 / 8) * εf * (qn : ℝ) + εf := by
  have hc : 0 < (19 / 8 : ℝ) * εf := by positivity
  obtain ⟨Q, hQ⟩ := exists_nat_ge (Real.log 2 / ((19 / 8 : ℝ) * εf))
  refine ⟨Q, fun qn hqn => ?_⟩
  have hQle : Real.log 2 / ((19 / 8 : ℝ) * εf) ≤ (Q : ℝ) := hQ
  have hle : (Q : ℝ) ≤ (qn : ℝ) := by exact_mod_cast hqn
  have hge : Real.log 2 / ((19 / 8 : ℝ) * εf) ≤ (qn : ℝ) := le_trans hQle hle
  have key : Real.log 2 ≤ (19 / 8 : ℝ) * εf * (qn : ℝ) := by
    have h := (div_le_iff₀ hc).mp hge
    rw [mul_comm (qn : ℝ)] at h
    exact h
  linarith [key, hL, hεf]

end Work.TMC16Core.Assembly

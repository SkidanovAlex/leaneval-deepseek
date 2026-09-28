import Mathlib

/-!
# Shared constants for the per-cell arithmetic of the `𝔡₃ > A^{1/20}` part (`(d,n) = (4,4)`)
-/

set_option autoImplicit false

namespace Work.HP.MDEstimates.hiparts

/-- The multiplicative constant `K = exp 2000` of the per-cell estimate. -/
noncomputable def hiK : ℝ := Real.exp 2000

/-- The target monomial `A^{68-1/32} B^{2-1/1000}`. -/
noncomputable def hiTgt (A B : ℝ) : ℝ := A ^ ((2175 : ℝ) / 32) * B ^ ((1999 : ℝ) / 1000)

lemma hiK_pos : 0 < hiK := Real.exp_pos 2000

lemma hiTgt_pos {A B : ℝ} (hA : 0 < A) (hB : 0 < B) : 0 < hiTgt A B := by
  unfold hiTgt
  positivity

end Work.HP.MDEstimates.hiparts

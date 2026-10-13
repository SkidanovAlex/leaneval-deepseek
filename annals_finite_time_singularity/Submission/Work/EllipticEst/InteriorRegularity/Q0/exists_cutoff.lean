import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Submission.Work.EllipticEst.InteriorRegularity.Q0.RRDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.Q0

set_option linter.unusedVariables false

/-- For `0 < A < L ≤ U < B` there is a smooth function `χ` with `χ = 1` on `[L,U]` and
`χ z ≠ 0 → A < z ∧ z < B` (i.e. the support of `χ` is contained in `(A,B)`).

Explicit witness: the product of the two Mathlib smooth transitions
`χ z = smoothTransition ((z - A)/(L - A)) * smoothTransition ((B - z)/(B - U))`. -/
theorem exists_cutoff {A L U B : ℝ} (hA : 0 < A) (hAL : A < L) (hLU : L ≤ U) (hUB : U < B) :
    ∃ χ : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n χ) ∧ (∀ z : ℝ, χ z ≠ 0 → A < z ∧ z < B) ∧
      (∀ z : ℝ, L ≤ z → z ≤ U → χ z = 1) := by
  have hLA : 0 < L - A := by linarith
  have hBU : 0 < B - U := by linarith
  refine ⟨fun z => Real.smoothTransition ((z - A) / (L - A))
      * Real.smoothTransition ((B - z) / (B - U)), ?_, ?_, ?_⟩
  · intro n
    exact (Real.smoothTransition.contDiff.comp
        ((contDiff_id.sub contDiff_const).div_const (L - A))).mul
      (Real.smoothTransition.contDiff.comp
        ((contDiff_const.sub contDiff_id).div_const (B - U)))
  · intro z hz
    dsimp only at hz
    have h1 : Real.smoothTransition ((z - A) / (L - A)) ≠ 0 := fun h => hz (by rw [h, zero_mul])
    have h2 : Real.smoothTransition ((B - z) / (B - U)) ≠ 0 := fun h => hz (by rw [h, mul_zero])
    have h1' : 0 < (z - A) / (L - A) := by
      by_contra hc
      exact h1 (Real.smoothTransition.zero_of_nonpos (not_lt.mp hc))
    have h2' : 0 < (B - z) / (B - U) := by
      by_contra hc
      exact h2 (Real.smoothTransition.zero_of_nonpos (not_lt.mp hc))
    exact ⟨sub_pos.mp ((div_pos_iff_of_pos_right hLA).mp h1'),
      sub_pos.mp ((div_pos_iff_of_pos_right hBU).mp h2')⟩
  · intro z hzL hzU
    dsimp only
    have h1 : 1 ≤ (z - A) / (L - A) := by rw [one_le_div hLA]; linarith
    have h2 : 1 ≤ (B - z) / (B - U) := by rw [one_le_div hBU]; linarith
    rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2,
      mul_one]

end Work.EllipticEst.InteriorRegularity.Q0

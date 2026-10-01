import Mathlib
import Submission.Work.LinnikAreas.Density4.thetaDiag_eval_defs

namespace Work.LinnikAreas.Density4

/-- The majorant `h n = n^{σ-1} e^{-n/A}` of the diagonal evaluation is antitone in `n`
for `σ ≤ 1` and `A > 0`: both factors `n ↦ n^{σ-1}` (with `σ - 1 ≤ 0`) and
`n ↦ e^{-n/A}` (with `A > 0`) are decreasing. -/
theorem thetaDiag_tdH_antitone (σ A : ℝ) (hσ : σ ≤ 1) (hA : 0 < A) :
    ∀ n : ℕ, 1 ≤ n → tdH σ A (n+1) ≤ tdH σ A n := by
  intro n hn
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hsm : 0 < (n:ℝ) := lt_of_lt_of_le one_pos hn1
  have h1 : ((n:ℝ)+1)^(σ-1) * Real.exp (-((n:ℝ)+1)/A) ≤ (n:ℝ)^(σ-1) * Real.exp (-(n:ℝ)/A) := by
    have hsl : (n:ℝ) ≤ (n:ℝ)+1 := by linarith
    have hpow : ((n:ℝ)+1)^(σ-1) ≤ (n:ℝ)^(σ-1) := Real.rpow_le_rpow_of_nonpos hsm hsl (by linarith)
    have hexp : Real.exp (-((n:ℝ)+1)/A) ≤ Real.exp (-(n:ℝ)/A) := by
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ hA.le
      linarith
    exact mul_le_mul hpow hexp (Real.exp_pos _).le (Real.rpow_nonneg hsm.le _)
  simpa [tdH, Nat.cast_add, Nat.cast_one] using h1

end Work.LinnikAreas.Density4

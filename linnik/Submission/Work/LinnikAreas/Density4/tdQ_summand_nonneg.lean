import Mathlib
import Submission.Work.LinnikAreas.Density4.thetaDiag_eval_defs

namespace Work.LinnikAreas.Density4

/-- Each summand of the saving sum `tdQ` is nonnegative on its range
`2 ≤ n ≤ ⌊e^{M-1}⌋`: the coefficient `M - log n - 1` is nonnegative because
`log n ≤ M - 1`, and the majorant `tdH σ A n` is a product of nonnegative
factors. -/
theorem tdQ_summand_nonneg (M σ A : ℝ) (hM : 15000 ≤ M) :
    ∀ n ∈ Finset.Icc 2 ⌊Real.exp (M-1)⌋₊,
      0 ≤ (M - Real.log (n:ℝ) - 1) * Work.LinnikAreas.Density4.tdH σ A n := by
  intro n hn
  rw [Finset.mem_Icc] at hn
  obtain ⟨h2, hnle⟩ := hn
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast h2
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  -- `n ≤ ⌊e^{M-1}⌋ ≤ e^{M-1}`
  have hnle' : (n:ℝ) ≤ Real.exp (M-1) := by
    have hfl := Nat.floor_le (Real.exp_pos (M-1)).le
    have hcast : (n:ℝ) ≤ (⌊Real.exp (M-1)⌋₊ : ℝ) := by exact_mod_cast hnle
    linarith
  -- hence `log n ≤ M - 1`
  have hlog : Real.log (n:ℝ) ≤ M - 1 := by
    have hmono := Real.log_le_log hnpos hnle'
    rwa [Real.log_exp] at hmono
  have hcoef : 0 ≤ M - Real.log (n:ℝ) - 1 := by linarith
  have hH : 0 ≤ tdH σ A n := by
    unfold tdH
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Real.exp_pos _).le
  exact mul_nonneg hcoef hH

end Work.LinnikAreas.Density4

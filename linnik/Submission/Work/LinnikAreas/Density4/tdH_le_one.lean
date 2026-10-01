import Mathlib
import Submission.Work.LinnikAreas.Density4.thetaDiag_eval_defs

namespace Work.LinnikAreas.Density4

theorem tdH_le_one (σ A : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hA : 0 < A)
    (n : ℕ) (hn : 1 ≤ n) : Work.LinnikAreas.Density4.tdH σ A n ≤ 1 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (σ - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have hexp : Real.exp (-(n : ℝ) / A) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) hA.le
  unfold tdH
  calc (n : ℝ) ^ (σ - 1) * Real.exp (-(n : ℝ) / A)
      ≤ 1 * 1 := mul_le_mul hpow hexp (Real.exp_pos _).le (by norm_num)
    _ = 1 := by ring

end Work.LinnikAreas.Density4

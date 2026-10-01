import Mathlib

namespace Work.LinnikAreas.Density4

lemma exp_div_le_log_div (n : ℕ) (hn : 1 ≤ n) (X : ℝ) (hX : 0 < X) :
    Real.exp (-(((n:ℝ) + 1) / X)) / ((n:ℝ) + 1) ≤ Real.log (((n:ℝ) + 1) / (n:ℝ)) := by
  have hn1 : (0:ℝ) < (n:ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn2 : (0:ℝ) < (n:ℝ) + 1 := by linarith
  -- The exponential factor is at most 1, so the left side is at most 1/(n+1).
  have hexp : Real.exp (-(((n:ℝ) + 1) / X)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith [div_pos hn2 hX]
  have h1 : Real.exp (-(((n:ℝ) + 1) / X)) / ((n:ℝ) + 1) ≤ 1 / ((n:ℝ) + 1) :=
    div_le_div_of_nonneg_right hexp (le_of_lt hn2)
  -- And 1/(n+1) ≤ log((n+1)/n), since log(1/(1-y)) ≥ y for y = 1/(n+1).
  have h2 : 1 / ((n:ℝ) + 1) ≤ Real.log (((n:ℝ) + 1) / (n:ℝ)) := by
    have hlog := Real.log_le_sub_one_of_pos (x := (n:ℝ) / ((n:ℝ) + 1)) (by positivity)
    have heq : ((n:ℝ) / ((n:ℝ) + 1))⁻¹ = ((n:ℝ) + 1) / (n:ℝ) := by field_simp
    have heq2 : Real.log (((n:ℝ) + 1) / (n:ℝ)) = - Real.log ((n:ℝ) / ((n:ℝ) + 1)) := by
      rw [← heq, Real.log_inv]
    rw [heq2]
    have hval : (n:ℝ) / ((n:ℝ) + 1) - 1 = -(1 / ((n:ℝ) + 1)) := by
      field_simp
      ring
    linarith
  linarith

end Work.LinnikAreas.Density4

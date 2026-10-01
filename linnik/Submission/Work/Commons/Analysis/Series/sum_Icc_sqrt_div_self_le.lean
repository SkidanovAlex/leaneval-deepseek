import Mathlib

namespace Work.Commons.Analysis.Series

/-- The elementary square-root sum bound `∑_{1 ≤ m ≤ N} √m / m ≤ 2√N` (equivalently `∑_{m ≤ N} m^{-1/2} ≤ 2√N`), obtained by telescoping `1/√m ≤ 2(√m − √(m−1))`. -/
theorem sum_Icc_sqrt_div_self_le (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, Real.sqrt (m : ℝ) / (m : ℝ)) ≤ 2 * Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    have hkey : Real.sqrt (((n+1 : ℕ) : ℝ)) / (((n+1 : ℕ) : ℝ))
        ≤ 2 * (Real.sqrt (((n+1:ℕ):ℝ)) - Real.sqrt ((n:ℝ))) := by
      push_cast
      have h1 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have ha : 0 < Real.sqrt ((n:ℝ)+1) := Real.sqrt_pos.mpr (by positivity)
      have hsq : (Real.sqrt ((n:ℝ)+1))^2 = (n:ℝ)+1 := Real.sq_sqrt (by positivity)
      have hb2 : (Real.sqrt (n:ℝ))^2 = (n:ℝ) := Real.sq_sqrt h1
      have hval : Real.sqrt ((n:ℝ)+1) / ((n:ℝ)+1) = 1 / Real.sqrt ((n:ℝ)+1) := by
        rw [div_eq_div_iff (by positivity) (ne_of_gt ha)]
        nlinarith [hsq]
      rw [hval]
      rw [div_le_iff₀ ha]
      nlinarith [sq_nonneg (Real.sqrt ((n:ℝ)+1) - Real.sqrt (n:ℝ))]
    nlinarith [ih, hkey, Real.sqrt_nonneg ((n:ℝ))]

end Work.Commons.Analysis.Series

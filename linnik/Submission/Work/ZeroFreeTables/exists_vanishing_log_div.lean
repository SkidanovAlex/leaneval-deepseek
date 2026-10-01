import Mathlib

namespace Work.ZeroFreeTables

/-- If `f` vanishes on `[x₀, ∞)`, then `f (log n / L)` vanishes for all large `n`,
provided `L > 0` (so that `log n / L → ∞`). -/
theorem exists_vanishing_log_div {x₀ L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f (Real.log n / L) = 0 := by
  have hLne : L ≠ 0 := ne_of_gt hL
  obtain ⟨m, hm⟩ := exists_nat_gt (Real.exp (x₀ * L))
  have hm_pos : (0 : ℝ) < (m : ℝ) := lt_trans (Real.exp_pos (x₀ * L)) hm
  refine ⟨m, fun n hn => hsupp _ ?_⟩
  have hlog_le : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hm_pos (Nat.cast_le.mpr hn)
  have hkey : x₀ * L ≤ Real.log (m : ℝ) :=
    le_of_lt (by rw [← Real.log_exp (x₀ * L)]; exact Real.log_lt_log (Real.exp_pos _) hm)
  have h : x₀ * L / L ≤ Real.log (n : ℝ) / L :=
    div_le_div_of_nonneg_right (le_trans hkey hlog_le) (le_of_lt hL)
  rwa [mul_div_cancel_right₀ x₀ hLne] at h

end Work.ZeroFreeTables

import Mathlib
import Submission.Work.WilE10.Psi

namespace Work.WilE10.Basic

/-- For `L : ℕ` and `|x| ≤ L`, the `L`-th power of the restricted exponential at `x / L`
recovers `exp x`.  (The case `L = 0` is degenerate and forces `x = 0`.) -/
theorem exp_eq_rexp_pow (L : ℕ) (x : ℝ) (h : |x| ≤ (L : ℝ)) :
    Real.exp x = WilkiesDesign.rexp (x / (L : ℝ)) ^ L := by
  rcases eq_or_lt_of_le (Nat.cast_nonneg (α := ℝ) L) with hL | hL
  · -- `L = 0`: the hypothesis forces `x = 0`.
    have hx : x = 0 := by
      have : |x| ≤ 0 := by simpa [← hL] using h
      exact abs_eq_zero.mp (le_antisymm this (abs_nonneg x))
    subst hx
    simp [WilkiesDesign.rexp]
  · -- `L > 0`: `x / L` lies in `[-1, 1]`, so `rexp` is `exp` there.
    have hLne : (L : ℝ) ≠ 0 := ne_of_gt hL
    have hle : |x / (L : ℝ)| ≤ 1 := by
      rw [abs_div, abs_of_pos hL, div_le_one hL]
      exact h
    rw [WilkiesDesign.rexp, if_pos hle]
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp

end Work.WilE10.Basic

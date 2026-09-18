import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Data.Nat

/-- For any natural numbers `L`, `d`, the real quotient `(L : ℝ) / (d : ℝ)` is
strictly less than the natural division rounded up by one:
`(L : ℝ) / (d : ℝ) < ((L / d : ℕ) : ℝ) + 1`. -/
theorem real_div_lt_nat_div_add_one (L d : ℕ) : (L : ℝ) / (d : ℝ) < ((L / d : ℕ) : ℝ) + 1 := by
  by_cases hd : d = 0
  · subst d
    simp
  · have hd0 : 0 < d := Nat.pos_of_ne_zero hd
    have hLnat : L < (L / d + 1) * d := by
      rw [← Nat.div_lt_iff_lt_mul hd0]
      exact Nat.lt_succ_self (L / d)
    have hLreal : (L : ℝ) < (((L / d + 1) * d : ℕ) : ℝ) := by
      exact_mod_cast hLnat
    have hconv : (((L / d + 1) * d : ℕ) : ℝ) = (((L / d : ℕ) : ℝ) + 1) * (d : ℝ) := by
      norm_cast
    have hdℝ : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    rw [hconv] at hLreal
    exact (div_lt_iff₀ hdℝ).2 hLreal

end Commons.Data.Nat
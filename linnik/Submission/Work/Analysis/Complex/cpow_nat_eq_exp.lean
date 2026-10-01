import Mathlib

namespace Work.Analysis.Complex

/-- For a natural number `n ≥ 1` and a real `t`, the complex power `n ^ (t * I)` agrees with
the principal branch of the exponential: `n ^ (t * I) = exp (I * (t * log n))`. -/
lemma cpow_nat_eq_exp (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    (n : ℂ) ^ ((t : ℂ) * Complex.I) = Complex.exp (Complex.I * ((t * Real.log (n : ℝ) : ℝ) : ℂ)) := by
  have hn0 : (n : ℂ) ≠ 0 := by
    have : (n : ℝ) ≠ 0 := by
      have : (0 : ℝ) < n := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
      positivity
    exact_mod_cast this
  rw [Complex.cpow_def, if_neg hn0]
  rw [← Complex.ofReal_natCast n]
  rw [← Complex.ofReal_log (show (0 : ℝ) ≤ n by positivity)]
  congr 1
  push_cast
  ring

end Work.Analysis.Complex

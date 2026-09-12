import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic

namespace Commons.Combinatorics.Fin

/-- Binomial expansion of `(4 + 1) ^ n`, i.e. `∑ t, n.choose t * 4 ^ t = 5 ^ n`. -/
theorem sum_choose_pow_four {n : ℕ} :
    (∑ t ∈ Finset.range (n + 1), (n.choose t : ℝ) * (4 : ℝ) ^ t) = (5 : ℝ) ^ n := by
  rw [show (5 : ℝ) = 4 + 1 by norm_num]
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro t ht
  have h1 : (1 : ℝ) ^ (n - t) = 1 := by simp
  rw [h1]
  ring

end Commons.Combinatorics.Fin
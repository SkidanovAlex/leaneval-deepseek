import Mathlib
import Submission.Commons.NumberTheory.Robin.robin_upper_le_55440

/-!
# Robin's inequality for `n ≥ 5041` from its validity for `n ≥ 55441`

If Robin's inequality holds for every `n ≥ 55441`, then it holds for every `n ≥ 5041`:
the intermediate range `5041 ≤ n ≤ 55440` is covered by the certified finite-range
lemma `robin_upper_le_55440`, and `n ≥ 55441` is the hypothesis `h`.
-/

namespace Commons.NumberTheory.Robin

theorem robin_upper_of_large (h : ∀ n : ℕ, 55441 ≤ n → ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤ Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ))) : ∀ n : ℕ, 5041 ≤ n → ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤ Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) := by
  intro n hn
  by_cases hle : n ≤ 55440
  · exact robin_upper_le_55440 n hn hle
  · have hn' : 55441 ≤ n := by omega
    exact h n hn'

end Commons.NumberTheory.Robin

import Mathlib
import Submission.Commons.NumberTheory.Robin.robin_pair_bridge

namespace Commons.NumberTheory.Robin

theorem robin_of_good_family (G : ℕ → Prop)
    (hstep : ∀ n : ℕ, 55441 ≤ n → ∃ N' N : ℕ,
      G N' ∧ G N ∧ 5040 ≤ N' ∧ N' < n ∧ n ≤ N ∧
      ∃ ε : ℝ, 0 < ε ∧
      Real.log (((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / (n : ℝ)) - ε * Real.log (n : ℝ) ≤
      Real.log (((ArithmeticFunction.sigma 1 N' : ℕ) : ℝ) / (N' : ℝ)) - ε * Real.log (N' : ℝ) ∧
      Real.log (((ArithmeticFunction.sigma 1 N' : ℕ) : ℝ) / (N' : ℝ)) - ε * Real.log (N' : ℝ) =
      Real.log (((ArithmeticFunction.sigma 1 N : ℕ) : ℝ) / (N : ℝ)) - ε * Real.log (N : ℝ))
    (hRobin : ∀ M : ℕ, G M → 5040 ≤ M →
      ((ArithmeticFunction.sigma 1 M : ℕ) : ℝ) ≤
        Real.exp Real.eulerMascheroniConstant * (M : ℝ) * Real.log (Real.log (M : ℝ))) :
    ∀ n : ℕ, 55441 ≤ n →
      ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
        Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) := by
  intro n hn
  rcases hstep n hn with ⟨N', N, hGN', hGN, h5040, hN'ltn, hnleN, hstep'⟩
  have h5040N : 5040 ≤ N := le_trans (le_trans h5040 (le_of_lt hN'ltn)) hnleN
  exact robin_pair_bridge h5040 hN'ltn hnleN (hRobin N' hGN' h5040) (hRobin N hGN h5040N) hstep'

end Commons.NumberTheory.Robin

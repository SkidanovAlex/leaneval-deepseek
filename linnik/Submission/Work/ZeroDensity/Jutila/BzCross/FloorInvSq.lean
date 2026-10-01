import Mathlib

namespace Work.ZeroDensity.Jutila.BzCross

open Finset

/-- **Uniform bound for the reciprocal-square weight.** For every `Q`,
`Σ_{q=1}^{Q} 1/q² ≤ 2`.
ROUTE: `q² ≥ q(q−1)` for `q ≥ 1`, and `1/(q(q−1)) = 1/(q−1) − 1/q`, so the tail
`Σ_{q=2}^{Q} 1/q² ≤ Σ_{q=2}^{Q} (1/(q−1) − 1/q) = 1 − 1/Q ≤ 1`, plus the `q = 1` term `1`. -/
theorem FloorInvSq (Q : ℕ) : ∑ q ∈ Finset.Icc 1 Q, 1 / ((q : ℝ) ^ 2) ≤ 2 := by
  have key : ∀ m : ℕ, 1 ≤ m → ∑ q ∈ Finset.Icc 1 m, 1 / ((q : ℝ) ^ 2) ≤ 2 - 1 / (m : ℝ) := by
    refine Nat.le_induction ?base ?step
    case base =>
      simp only [Finset.Icc_self, Finset.sum_singleton]
      norm_num
    case step =>
      intro m hm ih
      rw [Finset.sum_Icc_succ_top (f := fun q => 1 / ((q : ℝ) ^ 2)) (a := 1) (b := m)
        (by omega : 1 ≤ m + 1)]
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have hle : (m : ℝ) * ((m : ℝ) + 1) ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith [hmpos]
      have h1 : 1 / ((m : ℝ) + 1) ^ 2 ≤ 1 / ((m : ℝ) * ((m : ℝ) + 1)) :=
        one_div_le_one_div_of_le (by positivity) hle
      have h2 : 1 / ((m : ℝ) * ((m : ℝ) + 1)) = 1 / (m : ℝ) - 1 / ((m : ℝ) + 1) := by
        field_simp
        ring
      have hstep : 1 / ((↑(m + 1) : ℝ)) ^ 2 ≤ 1 / (m : ℝ) - 1 / (↑(m + 1) : ℝ) := by
        push_cast
        linarith
      linarith [ih, hstep]
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · subst hQ
    simp
  · have h := key Q hQ
    have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
    have : (0 : ℝ) ≤ 1 / (Q : ℝ) := by positivity
    linarith

end Work.ZeroDensity.Jutila.BzCross

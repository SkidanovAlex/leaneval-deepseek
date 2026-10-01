import Mathlib

open scoped BigOperators

namespace Work.ZeroFreeTables

/-- If each of `a₁, …, a₆ : ℕ → ℝ` vanishes for `n ≥ N`, and if every term of
the combined sequence is nonnegative, then the weighted sum of the (finite)
total sums is nonnegative. -/
theorem combination_six_nonneg {N : ℕ} {c₁ c₂ c₃ : ℝ} {a₁ a₂ a₃ a₄ a₅ a₆ : ℕ → ℝ}
    (h₁ : ∀ n : ℕ, N ≤ n → a₁ n = 0) (h₂ : ∀ n : ℕ, N ≤ n → a₂ n = 0)
    (h₃ : ∀ n : ℕ, N ≤ n → a₃ n = 0) (h₄ : ∀ n : ℕ, N ≤ n → a₄ n = 0)
    (h₅ : ∀ n : ℕ, N ≤ n → a₅ n = 0) (h₆ : ∀ n : ℕ, N ≤ n → a₆ n = 0)
    (hterm : ∀ n : ℕ, 0 ≤ c₁ * (a₁ n + a₂ n) + c₂ * (a₃ n + a₄ n) + c₃ * (a₅ n + a₆ n)) :
    0 ≤ c₁ * ((∑' n : ℕ, a₁ n) + (∑' n : ℕ, a₂ n))
      + c₂ * ((∑' n : ℕ, a₃ n) + (∑' n : ℕ, a₄ n))
      + c₃ * ((∑' n : ℕ, a₅ n) + (∑' n : ℕ, a₆ n)) := by
  -- Each series is really a finite sum over `Finset.range N`.
  have e1 : (∑' n : ℕ, a₁ n) = ∑ n ∈ Finset.range N, a₁ n :=
    tsum_eq_sum (fun n hn => h₁ n (Nat.le_of_not_lt (by simpa using hn)))
  have e2 : (∑' n : ℕ, a₂ n) = ∑ n ∈ Finset.range N, a₂ n :=
    tsum_eq_sum (fun n hn => h₂ n (Nat.le_of_not_lt (by simpa using hn)))
  have e3 : (∑' n : ℕ, a₃ n) = ∑ n ∈ Finset.range N, a₃ n :=
    tsum_eq_sum (fun n hn => h₃ n (Nat.le_of_not_lt (by simpa using hn)))
  have e4 : (∑' n : ℕ, a₄ n) = ∑ n ∈ Finset.range N, a₄ n :=
    tsum_eq_sum (fun n hn => h₄ n (Nat.le_of_not_lt (by simpa using hn)))
  have e5 : (∑' n : ℕ, a₅ n) = ∑ n ∈ Finset.range N, a₅ n :=
    tsum_eq_sum (fun n hn => h₅ n (Nat.le_of_not_lt (by simpa using hn)))
  have e6 : (∑' n : ℕ, a₆ n) = ∑ n ∈ Finset.range N, a₆ n :=
    tsum_eq_sum (fun n hn => h₆ n (Nat.le_of_not_lt (by simpa using hn)))
  rw [e1, e2, e3, e4, e5, e6]
  -- Rewrite the right-hand side as a single finite sum of the individual terms.
  have key : ∑ n ∈ Finset.range N,
        (c₁ * (a₁ n + a₂ n) + c₂ * (a₃ n + a₄ n) + c₃ * (a₅ n + a₆ n))
      = c₁ * ((∑ n ∈ Finset.range N, a₁ n) + (∑ n ∈ Finset.range N, a₂ n))
        + c₂ * ((∑ n ∈ Finset.range N, a₃ n) + (∑ n ∈ Finset.range N, a₄ n))
        + c₃ * ((∑ n ∈ Finset.range N, a₅ n) + (∑ n ∈ Finset.range N, a₆ n)) := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← key]
  exact Finset.sum_nonneg (fun n _ => hterm n)

end Work.ZeroFreeTables

import Mathlib

namespace Work.ZeroFreeTables

theorem tsum_finset_sum_nonneg {g : ℕ → ℕ → ℝ} {N : ℕ} {c : ℕ → ℝ} {d : ℕ}
    (hvan : ∀ k n : ℕ, N ≤ n → g k n = 0)
    (hterm : ∀ n : ℕ, 0 ≤ ∑ k ∈ Finset.range (d + 1), c k * g k n) :
    0 ≤ ∑ k ∈ Finset.range (d + 1), c k * (∑' n : ℕ, g k n) := by
  have h1 : ∀ k, (∑' n : ℕ, g k n) = ∑ n ∈ Finset.range N, g k n := fun k =>
    tsum_eq_sum (fun n hn => hvan k n (Nat.le_of_not_lt (by simpa using hn)))
  calc 0 ≤ ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range (d + 1), c k * g k n :=
        Finset.sum_nonneg (fun n _ => hterm n)
    _ = ∑ k ∈ Finset.range (d + 1), ∑ n ∈ Finset.range N, c k * g k n :=
        Finset.sum_comm
    _ = ∑ k ∈ Finset.range (d + 1), c k * (∑' n : ℕ, g k n) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [h1 k, Finset.mul_sum]

end Work.ZeroFreeTables

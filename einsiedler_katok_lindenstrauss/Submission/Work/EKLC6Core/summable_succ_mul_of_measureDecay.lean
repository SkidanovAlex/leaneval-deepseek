import Mathlib

/-!
# Weighted summability from measure decay

Given nonnegative sequences `a, b : ℕ → ℝ` with `b n = b (n+1) + a (n+1)` (so `b` is
nonincreasing with differences `a`) and with bounded partial sums `∑_{m<N} b m ≤ 1`, we
show that `∑ (n+1) * a (n+1)` converges and has sum at most `1`.

The proof is a telescoping/Abel summation: writing `a (n+1) = b n - b (n+1)`,

  `∑_{n<N} (n+1) * a (n+1) = ∑_{n<N} (n+1) * (b n - b (n+1)) = ∑_{n<N} b n - N * b N ≤ 1`,

where the last step uses `∑_{n<N} b n ≤ 1` and `N * b N ≥ 0`. Nonnegative terms with
uniformly bounded partial sums are summable (`summable_of_sum_range_le`).
-/

namespace Work.EKLC6Core

/-- Telescoping/Abel identity:
`∑_{n<N} (n+1) * (b n - b (n+1)) = ∑_{n<N} b n - N * b N`. -/
lemma sum_range_succ_mul_sub (b : ℕ → ℝ) (N : ℕ) :
    ∑ i ∈ Finset.range N, ((i : ℝ) + 1) * (b i - b (i + 1))
      = ∑ i ∈ Finset.range N, b i - (N : ℝ) * b N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    push_cast
    ring

theorem summable_succ_mul_of_measureDecay {a b : ℕ → ℝ} (ha : ∀ n : ℕ, 0 ≤ a n)
    (hb : ∀ n : ℕ, 0 ≤ b n) (hstep : ∀ n : ℕ, b n = b (n + 1) + a (n + 1))
    (hupper : ∀ N : ℕ, ∑ m ∈ Finset.range N, b m ≤ 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * a (n + 1)) ∧
      (∑' n : ℕ, ((n : ℝ) + 1) * a (n + 1)) ≤ 1 := by
  have hnonneg : ∀ n : ℕ, 0 ≤ ((n : ℝ) + 1) * a (n + 1) := by
    intro n
    exact mul_nonneg (by positivity) (ha (n + 1))
  have hdiff : ∀ n : ℕ, a (n + 1) = b n - b (n + 1) := by
    intro n
    have := hstep n
    linarith
  have hbound : ∀ N : ℕ, ∑ n ∈ Finset.range N, ((n : ℝ) + 1) * a (n + 1) ≤ 1 := by
    intro N
    have hsum : ∑ n ∈ Finset.range N, ((n : ℝ) + 1) * a (n + 1)
        = ∑ n ∈ Finset.range N, ((n : ℝ) + 1) * (b n - b (n + 1)) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hdiff n]
    rw [hsum, sum_range_succ_mul_sub b N]
    have hbN : 0 ≤ (N : ℝ) * b N := mul_nonneg (by positivity) (hb N)
    linarith [hupper N]
  exact ⟨summable_of_sum_range_le hnonneg hbound, Real.tsum_le_of_sum_range_le hnonneg hbound⟩

end Work.EKLC6Core

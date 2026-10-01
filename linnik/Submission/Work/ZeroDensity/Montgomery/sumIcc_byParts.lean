import Mathlib

namespace Work.ZeroDensity.Montgomery

open scoped Classical BigOperators

/-- Reindex an `Icc 1 N` sum as a `range N` sum: `∑_{n=1}^{N} f n = ∑_{n<N} f (n+1)`. -/
lemma sum_Icc_one_eq_sum_range (f : ℕ → ℂ) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, f k = ∑ k ∈ Finset.range N, f (k + 1) := by
  have h : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [h, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  exact Finset.sum_congr rfl (fun k _ => by rw [Nat.add_comm])

/-- **Summation by parts (Abel transformation) for `Finset.Icc 1 N`.**  For any `N : ℕ` and any
`x w : ℕ → ℂ`,
`∑_{n≤N} x n · w n = w N · ∑_{k≤N} x k + ∑_{n≤N-1} (w n - w (n+1)) · ∑_{k≤n} x k`.
(With `X n = ∑_{k≤n} x k` one has `x n = X n - X (n-1)` and telescoping gives the identity;
both sides vanish for `N = 0`.) -/
theorem sumIcc_byParts (N : ℕ) (x w : ℕ → ℂ) :
    ∑ n ∈ Finset.Icc 1 N, x n * w n
      = w N * (∑ k ∈ Finset.Icc 1 N, x k)
        + ∑ n ∈ Finset.Icc 1 (N - 1), (w n - w (n + 1)) * (∑ k ∈ Finset.Icc 1 n, x k) := by
  rcases N with _ | M
  · simp
  · simp only [sum_Icc_one_eq_sum_range, Nat.succ_sub_one]
    have key := Finset.sum_range_by_parts (fun i => w (i + 1)) (fun i => x (i + 1)) (M + 1)
    simp only [smul_eq_mul, Nat.succ_sub_one, Nat.add_assoc] at key
    rw [Finset.sum_congr rfl
          (fun i (_ : i ∈ Finset.range (M+1)) => mul_comm (x (i+1)) (w (i+1))), key]
    rw [show (∑ i ∈ Finset.range M, (w (i + 1) - w (i + 2)) * ∑ j ∈ Finset.range (i + 1), x (j + 1))
          = - ∑ i ∈ Finset.range M, (w (i + 2) - w (i + 1)) * ∑ j ∈ Finset.range (i + 1), x (j + 1) by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring]
    ring

end Work.ZeroDensity.Montgomery

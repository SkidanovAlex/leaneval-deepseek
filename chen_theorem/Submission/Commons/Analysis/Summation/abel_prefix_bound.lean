import Mathlib.Analysis.CStarAlgebra.Classes

namespace Commons.Analysis.Summation

open Finset
open scoped BigOperators

/-- Abel summation by parts over the window `Icc N M`, expressing the sum via the
partial (prefix) sums `Σ_{k=N}^{n} a k` starting at `N`:
`Σ_{n=N}^{M} a n b n = (Σ_{n=N}^{M} a n) b M + Σ_{n=N}^{M-1} (Σ_{k=N}^{n} a k)(b n - b (n+1))`. -/
private lemma abel_window_from_N (a b : ℕ → ℂ) {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∑ n ∈ Finset.Icc N M, a n * b n)
      = (∑ k ∈ Finset.Icc N M, a k) * b M
        + ∑ n ∈ Finset.Icc N (M - 1), (∑ k ∈ Finset.Icc N n, a k) * (b n - b (n + 1)) := by
  induction M, hNM using Nat.le_induction with
  | base =>
      have hempty : Finset.Icc N (N - 1) = ∅ := by
        rw [Finset.Icc_eq_empty_iff]; omega
      rw [hempty, Finset.sum_empty]
      simp [Finset.Icc_self]
  | succ m hm ih =>
      have hmm : m + 1 - 1 = m := by omega
      rw [hmm]
      have hsum1 : (∑ n ∈ Finset.Icc N (m + 1), a n * b n)
          = (∑ n ∈ Finset.Icc N m, a n * b n) + a (m + 1) * b (m + 1) :=
        Finset.sum_Icc_succ_top (by omega) (fun n => a n * b n)
      have hsum2 : (∑ k ∈ Finset.Icc N (m + 1), a k)
          = (∑ k ∈ Finset.Icc N m, a k) + a (m + 1) :=
        Finset.sum_Icc_succ_top (by omega) a
      have hsplit : (∑ n ∈ Finset.Icc N m, (∑ k ∈ Finset.Icc N n, a k) * (b n - b (n + 1)))
          = (∑ n ∈ Finset.Icc N (m - 1), (∑ k ∈ Finset.Icc N n, a k) * (b n - b (n + 1)))
            + (∑ k ∈ Finset.Icc N m, a k) * (b m - b (m + 1)) := by
        have := Finset.sum_Icc_succ_top (a := N) (b := m - 1) (by omega : N ≤ (m - 1) + 1)
          (fun n => (∑ k ∈ Finset.Icc N n, a k) * (b n - b (n + 1)))
        rwa [show (m - 1) + 1 = m from by omega] at this
      rw [hsum1, hsum2, hsplit, ih]
      ring

/-- Abel summation by parts over `Icc N M`, with the bound on the *prefix* sums
`Σ_{k=N}^{n} a k` (rather than on all interval sums). -/
theorem abel_prefix_bound (a b : ℕ → ℂ) (B : ℝ) {N M : ℕ} (hNM : N ≤ M) (hN : 1 ≤ N)
    (hB : ∀ n, N ≤ n → n ≤ M → ‖∑ k ∈ Finset.Icc N n, a k‖ ≤ B) :
    ‖∑ k ∈ Finset.Icc N M, a k * b k‖
      ≤ B * ‖b M‖ + B * (∑ n ∈ Finset.Icc N (M - 1), ‖b n - b (n + 1)‖) := by
  rw [abel_window_from_N a b hN hNM]
  refine le_trans (norm_add_le _ _) (add_le_add ?h1 ?h2)
  · calc ‖(∑ k ∈ Finset.Icc N M, a k) * b M‖
        = ‖∑ k ∈ Finset.Icc N M, a k‖ * ‖b M‖ := norm_mul _ _
      _ ≤ B * ‖b M‖ := mul_le_mul_of_nonneg_right (hB M hNM le_rfl) (norm_nonneg _)
  · calc ‖∑ n ∈ Finset.Icc N (M - 1),
            (∑ k ∈ Finset.Icc N n, a k) * (b n - b (n + 1))‖
        ≤ ∑ n ∈ Finset.Icc N (M - 1),
            ‖(∑ k ∈ Finset.Icc N n, a k) * (b n - b (n + 1))‖ :=
            norm_sum_le _ _
      _ = ∑ n ∈ Finset.Icc N (M - 1),
            ‖∑ k ∈ Finset.Icc N n, a k‖ * ‖b n - b (n + 1)‖ :=
            Finset.sum_congr rfl (fun n _ => norm_mul _ _)
      _ ≤ ∑ n ∈ Finset.Icc N (M - 1), B * ‖b n - b (n + 1)‖ := by
            apply Finset.sum_le_sum
            intro n hn
            rw [Finset.mem_Icc] at hn
            exact mul_le_mul_of_nonneg_right (hB n hn.1 (by omega)) (norm_nonneg _)
      _ = B * ∑ n ∈ Finset.Icc N (M - 1), ‖b n - b (n + 1)‖ := by
            rw [Finset.mul_sum]

end Commons.Analysis.Summation
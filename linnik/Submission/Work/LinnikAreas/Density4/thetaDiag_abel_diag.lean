import Mathlib
import Submission.Work.LinnikAreas.Density4.abel_sum_Icc

namespace Work.LinnikAreas.Density4

/-- Abel summation (partial summation) in the shifted form used for the diagonal
term: summing the differences `X n - X (n-1)` weighted by `H n` and adding the
boundary term `X 1 * H 2` leaves a boundary term `X (M+1) * H (M+1)` plus a sum
of `X n` against the differences of `H`. -/
lemma abel_diag_shifted (X H : ℕ → ℝ) (M : ℕ) (hM : 1 ≤ M) :
    ∑ n ∈ Finset.Icc 2 (M+1), (X n - X (n-1)) * H n + X 1 * H 2
      = X (M+1) * H (M+1) + ∑ n ∈ Finset.Icc 2 M, X n * (H n - H (n+1)) := by
  induction M, hM using Nat.le_induction with
  | base =>
    have e1 : Finset.Icc 2 (1 + 1) = {2} := by simp [Finset.Icc_self]
    have e2 : Finset.Icc 2 1 = ∅ := by
      rw [Finset.Icc_eq_empty]; norm_num
    rw [e1, e2]
    simp
    ring
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (a := 2) (b := n + 1) (by omega)
          (fun k => (X k - X (k-1)) * H k)]
    rw [Finset.sum_Icc_succ_top (a := 2) (b := n) (by omega)
          (fun k => X k * (H k - H (k+1)))]
    simp only [Nat.add_sub_cancel]
    have hA : ∑ k ∈ Finset.Icc 2 (n+1), (X k - X (k-1)) * H k
        = X (n+1) * H (n+1) + ∑ k ∈ Finset.Icc 2 n, X k * (H k - H (k+1)) - X 1 * H 2 := by
      linarith [ih]
    rw [hA]
    ring

theorem thetaDiag_abel_diag (X H : ℕ → ℝ) (N : ℕ) (hN : 2 ≤ N) :
    ∑ n ∈ Finset.Icc 2 N, (X n - X (n-1)) * H n + X 1 * H 2
      = X N * H N + ∑ n ∈ Finset.Icc 2 (N-1), X n * (H n - H (n+1)) := by
  have h := abel_diag_shifted X H (N-1) (by omega)
  rwa [show N - 1 + 1 = N by omega] at h

end Work.LinnikAreas.Density4

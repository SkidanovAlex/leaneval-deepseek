import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Submission.Commons.Data.Nat.card_multiples_window_bound

namespace Commons.Data.Nat

/-- Generalized form of `list_zipIdx_sum_eq_range`, where the indexing of `zipIdx`
starts at `k` rather than `0`.  This is the natural induction-friendly statement. -/
theorem list_zipIdx_sum_eq_range_aux (B : ℕ) (l : List ℕ) (k : ℕ) :
    ((l.zipIdx k).map (fun p => p.1 * B ^ p.2)).sum
      = ∑ i ∈ Finset.range l.length, l.getD i 0 * B ^ (k + i) := by
  induction l generalizing k with
  | nil => simp
  | cons a t ih =>
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, List.length_cons, ih (k + 1)]
    rw [Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
    have hS : (∑ i ∈ Finset.range t.length, t.getD i 0 * B ^ (k + 1 + i))
        = ∑ i ∈ Finset.range t.length, t.getD i 0 * B ^ (k + (i + 1)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show k + 1 + i = k + (i + 1) from by omega]
    rw [hS, Nat.add_comm (a * B ^ k)]

theorem list_zipIdx_sum_eq_range (B : ℕ) (u : List ℕ) :
    (u.zipIdx.map (fun p => p.1 * B ^ p.2)).sum
      = ∑ i ∈ Finset.range u.length, u.getD i 0 * B ^ i := by
  simpa using list_zipIdx_sum_eq_range_aux B u 0

end Commons.Data.Nat
import Mathlib

namespace Work.Pert.RBlock6

theorem walk_dev_le {F : ℂ → ℂ} {G : ℂ → ℝ} {ς : ℂ} {N : ℕ}
    (h : ∀ j : ℕ, j < N → ‖F (F^[j] ς) - (F^[j] ς + 1)‖ ≤ G (F^[j] ς)) :
    ‖F^[N] ς - (ς + (N : ℂ))‖ ≤ ∑ j ∈ Finset.range N, G (F^[j] ς) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hstep : ‖F (F^[n] ς) - (F^[n] ς + 1)‖ ≤ G (F^[n] ς) :=
      h n (Nat.lt_succ_self n)
    have hih : ‖F^[n] ς - (ς + (n : ℂ))‖ ≤ ∑ j ∈ Finset.range n, G (F^[j] ς) :=
      ih (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self n)))
    rw [Finset.sum_range_succ]
    calc ‖F^[n+1] ς - (ς + ((n + 1 : ℕ) : ℂ))‖
        = ‖(F (F^[n] ς) - (F^[n] ς + 1)) + (F^[n] ς - (ς + (n : ℂ)))‖ := by
          rw [Function.iterate_succ_apply']; congr 1; push_cast; ring
      _ ≤ ‖F (F^[n] ς) - (F^[n] ς + 1)‖ + ‖F^[n] ς - (ς + (n : ℂ))‖ := norm_add_le _ _
      _ ≤ ∑ j ∈ Finset.range n, G (F^[j] ς) + G (F^[n] ς) := by linarith

end Work.Pert.RBlock6

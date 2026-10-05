import Mathlib

namespace Work.RPCore.Chain

lemma seq_zero_of_step {n : ℕ} (V : ℕ → ℝ)
    (h0 : V 0 = 0) (h : ∀ m, 0 < m → m < n → V (m-1) = V m) :
    ∀ m, m < n → V m = 0 := by
  intro m
  induction m with
  | zero => intro _; exact h0
  | succ k ih =>
    intro hk
    have hstep : V k = V (k + 1) := by
      have := h (k + 1) (Nat.succ_pos k) hk
      simpa using this
    rw [← hstep]
    exact ih (Nat.lt_of_succ_lt hk)

end Work.RPCore.Chain

import Mathlib

namespace Work.RPCore.Chain

lemma seq_zero_of_step_right {n : ℕ} (V : ℕ → ℝ) (a : ℕ) (hn : 1 ≤ n)
    (h : ∀ m, a < m → m < n → V (m-1) = V m) (hlast : V (n-1) = 0) :
    ∀ m, a ≤ m → m < n → V m = 0 := by
  -- Descend from `n - 1` to `a`, using the step relation `V (m-1) = V m`.
  have key : ∀ k m, n - 1 - m = k → a ≤ m → m < n → V m = 0 := by
    intro k
    induction k with
    | zero =>
      -- `n - 1 - m = 0` forces `m = n - 1`, where `V` vanishes by `hlast`.
      intro m hm hle hlt
      have : m = n - 1 := by omega
      rw [this, hlast]
    | succ k ih =>
      -- `n - 1 - m = k + 1` gives `m < n - 1`, so `V m = V (m+1)` and we recurse.
      intro m hm hle hlt
      have hstep : V m = V (m+1) := by
        have := h (m+1) (by omega) (by omega)
        simpa using this
      rw [hstep]
      exact ih (m+1) (by omega) (by omega) (by omega)
  intro m hle hlt
  exact key (n - 1 - m) m rfl hle hlt

end Work.RPCore.Chain

import Mathlib

namespace Work.RPCore.Chain

lemma seq_const_of_step {n : ℕ} (B : ℕ → ℝ) (a : ℕ)
    (h : ∀ m, a ≤ m → m < n → B (m+1) = B m) :
    ∀ m, a ≤ m → m ≤ n → B m = B a := by
  intro m hm
  refine Nat.le_induction (P := fun k (_ : a ≤ k) => k ≤ n → B k = B a) ?base ?step m hm
  · intro _; rfl
  · intro k hk ih hkn
    have hstep : B (k + 1) = B k := h k hk (by omega)
    rw [hstep]
    exact ih (by omega)

end Work.RPCore.Chain

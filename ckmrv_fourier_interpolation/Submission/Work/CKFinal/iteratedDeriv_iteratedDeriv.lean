import Mathlib

namespace Work.CKFinal

/-- The `n`-th derivative of the `l`-th derivative is the `(l + n)`-th derivative. -/
lemma iteratedDeriv_iteratedDeriv (f : ℝ → ℂ) (l n : ℕ) :
    iteratedDeriv n (iteratedDeriv l f) = iteratedDeriv (l + n) f := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc iteratedDeriv (n + 1) (iteratedDeriv l f)
        = deriv (iteratedDeriv n (iteratedDeriv l f)) := iteratedDeriv_succ
      _ = deriv (iteratedDeriv (l + n) f) := by rw [ih]
      _ = iteratedDeriv (l + n + 1) f := by rw [iteratedDeriv_succ]
      _ = iteratedDeriv (l + (n + 1)) f := by rw [Nat.add_assoc]

end Work.CKFinal

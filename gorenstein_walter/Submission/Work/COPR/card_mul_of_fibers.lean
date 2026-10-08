import Mathlib

namespace Work.COPR

set_option linter.style.haveILetI false in
/-- If every fiber of `f : α → β` has cardinality `k`, then `|α| = |β| * k`.
This holds even when `f` is not surjective: then some (hence every) fiber is
empty, forcing `k = 0` and `α` empty.  The proof decomposes `α` along the fibers
of `f` via `Equiv.sigmaFiberEquiv` and sums the cardinalities. -/
theorem card_mul_of_fibers {α β : Type*} [Finite α] [Finite β]
    (f : α → β) (k : ℕ) (h : ∀ b, Nat.card {a : α | f a = b} = k) :
    Nat.card α = Nat.card β * k := by
  letI := Fintype.ofFinite β
  calc Nat.card α
      = Nat.card ((y : β) × {x : α // f x = y}) :=
        Nat.card_congr (Equiv.sigmaFiberEquiv f).symm
    _ = ∑ b : β, Nat.card {a : α // f a = b} := Nat.card_sigma
    _ = ∑ b : β, k := by
          apply Finset.sum_congr rfl
          intro b _
          exact h b
    _ = Nat.card β * k := by
          rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
          simp

end Work.COPR

import Mathlib.SetTheory.Cardinal.Finite

namespace Commons.Combinatorics.Pigeonhole

/-- **Pigeonhole principle**, cardinal form: if `β` is finite and there are strictly fewer
elements in `β` than in `α`, then any map `α → β` identifies two distinct elements of `α`.
(If `α` is infinite then `Nat.card α = 0`, so the hypothesis is vacuous.) -/
theorem exists_ne_of_card_lt_finite {α β : Type*} [Finite β] (f : α → β)
    (h : Nat.card β < Nat.card α) : ∃ a b : α, a ≠ b ∧ f a = f b := by
  by_contra hc
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    exact hc ⟨a, b, hne, hab⟩
  have hle := Nat.card_le_card_of_injective f hinj
  omega

end Commons.Combinatorics.Pigeonhole
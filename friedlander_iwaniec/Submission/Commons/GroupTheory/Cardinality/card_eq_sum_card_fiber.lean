import Mathlib.Data.Fintype.BigOperators

namespace Commons.GroupTheory.Cardinality

/-- The cardinal of a finite type is the sum, over all `b : β`, of the cardinals of
the fibers of `f` above `b`. -/
theorem card_eq_sum_card_fiber {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (f : α → β) :
    Fintype.card α = ∑ b : β, Fintype.card {a : α // f a = b} := by
  calc
    Fintype.card α = Fintype.card (Sigma fun b : β => {a : α // f a = b}) := by
      exact (Fintype.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ b : β, Fintype.card {a : α // f a = b} := Fintype.card_sigma

end Commons.GroupTheory.Cardinality
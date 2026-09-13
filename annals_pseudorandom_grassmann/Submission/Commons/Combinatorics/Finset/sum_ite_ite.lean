import Mathlib.Algebra.Ring.Rat
import Mathlib.SetTheory.Cardinal.Finite

namespace Commons.Combinatorics.Finset

theorem sum_ite_ite {α β : Type*} [Fintype α] [Fintype β] (p : α → Prop) [DecidablePred p]
    (q : α → β → Prop) [∀ a, DecidablePred (q a)] (f : β → ℚ) :
    (∑ a : α, if p a then (∑ b : β, if q a b then f b else 0) else 0) =
      ∑ b : β, f b * (Nat.card {a : α // p a ∧ q a b} : ℚ) := by
  have h1 : (∑ a : α, if p a then (∑ b : β, if q a b then f b else 0) else 0) =
      ∑ a : α, ∑ b : β, if p a ∧ q a b then f b else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases hp : p a <;> simp [hp]
  rw [h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [mul_comm]

end Commons.Combinatorics.Finset
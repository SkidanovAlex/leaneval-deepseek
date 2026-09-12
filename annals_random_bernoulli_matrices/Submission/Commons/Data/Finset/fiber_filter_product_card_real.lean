import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Data.Finset

/-- The cardinality (as a real) of the filter on a product by a predicate on the
first coordinate and a first-coordinate-dependent predicate on the second
coordinate equals the sum over the good first coordinates of the cardinalities
of the fibres. -/
theorem fiber_filter_product_card_real {α β : Type} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (P : α → Prop) [DecidablePred P]
    (Q : α → β → Prop) [∀ a, DecidablePred (Q a)] :
    ((((s.product t).filter (fun p : α × β => P p.1 ∧ Q p.1 p.2)).card : ℕ) : ℝ) =
      (∑ a ∈ (s.filter P), (((t.filter (fun b : β => Q a b)).card : ℕ) : ℝ)) := by
  classical
  have hnat :
      (((s.product t).filter (fun p : α × β => P p.1 ∧ Q p.1 p.2)).card : ℕ) =
        ∑ a ∈ (s.filter P), ((t.filter (fun b : β => Q a b)).card : ℕ) := by
    rw [Finset.card_filter]
    rw [show (∑ i ∈ s.product t, if P i.1 ∧ Q i.1 i.2 then (1 : ℕ) else 0) =
        ∑ a ∈ s, ∑ b ∈ t, (if P a ∧ Q a b then (1 : ℕ) else 0) by
      simpa using (Finset.sum_product (s := s) (t := t)
        (f := fun p : α × β => if P p.1 ∧ Q p.1 p.2 then (1 : ℕ) else 0))]
    have hinner : ∀ a ∈ s, (∑ b ∈ t, (if P a ∧ Q a b then (1 : ℕ) else 0)) =
        if P a then (∑ b ∈ t, (if Q a b then (1 : ℕ) else 0)) else 0 := by
      intro a ha
      by_cases hP : P a
      · simp [hP]
      · simp [hP]
    rw [Finset.sum_congr rfl hinner]
    rw [← Finset.sum_filter (fun a : α => P a)]
    congr 1
    ext a
    simp
  exact_mod_cast hnat

end Commons.Data.Finset
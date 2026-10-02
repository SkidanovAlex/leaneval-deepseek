import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Commons.Data.Finset

/-- Double counting: the number of pairs `(x, y) ∈ s × t` with `r x y`, summed
first over `x` and then over `y`, is the same. -/
theorem sum_card_filter_comm {α β : Type*} (s : Finset α) (t : Finset β)
    (r : α → β → Prop) [DecidableRel r] :
    s.sum (fun x : α => (t.filter (fun y : β => r x y)).card) =
      t.sum (fun y : β => (s.filter (fun x : α => r x y)).card) := by
  classical
  calc
    s.sum (fun x : α => (t.filter (fun y : β => r x y)).card)
        = ∑ x ∈ s, ∑ y ∈ t, (if r x y then (1 : ℕ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            rw [Finset.card_filter]
    _ = ∑ y ∈ t, ∑ x ∈ s, (if r x y then (1 : ℕ) else 0) := by
            simpa using (Finset.sum_comm (s := s) (t := t)
              (f := fun (x : α) (y : β) => if r x y then (1 : ℕ) else 0))
    _ = t.sum (fun y : β => (s.filter (fun x : α => r x y)).card) := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            rw [Finset.card_filter]

end Commons.Data.Finset
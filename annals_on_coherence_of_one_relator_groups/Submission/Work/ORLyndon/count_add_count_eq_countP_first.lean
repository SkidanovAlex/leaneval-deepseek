import Mathlib

namespace Work.ORLyndon

theorem count_add_count_eq_countP_first {α : Type*} [DecidableEq α] (x : α) (L : List (α × Bool)) :
    L.count (x, true) + L.count (x, false)
      = List.countP (fun p : α × Bool => decide (p.1 = x)) L := by
  induction L with
  | nil => simp
  | cons p t ih =>
    rw [List.count_cons, List.count_cons, List.countP_cons]
    have h : (if (p == (x, true)) = true then 1 else 0)
        + (if (p == (x, false)) = true then 1 else 0)
        = (if decide (p.1 = x) then 1 else 0) := by
      cases p with
      | mk a b => cases b <;> simp
    omega

end Work.ORLyndon

import Mathlib

universe u

namespace Work.OROneRel

theorem append_take_rotate_drop {α : Type u} (W : List α) {n : ℕ} (hn : n ≤ W.length) :
    W ++ W = W.take n ++ W.rotate n ++ W.drop n := by
  rw [List.rotate_eq_drop_append_take hn]
  have h : W.take n ++ W.drop n = W := List.take_append_drop n W
  conv_lhs => rw [← h]
  simp only [List.append_assoc]

end Work.OROneRel

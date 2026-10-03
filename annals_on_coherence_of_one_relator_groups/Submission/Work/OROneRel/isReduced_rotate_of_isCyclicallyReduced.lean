import Mathlib

universe u

namespace Work.OROneRel

open List

theorem isReduced_rotate_of_isCyclicallyReduced {α : Type u} {W : List (α × Bool)}
    (h : FreeGroup.IsCyclicallyReduced W) (n : ℕ) : FreeGroup.IsReduced (W.rotate n) := by
  -- `W ++ W` is reduced because `W` is cyclically reduced.
  have hfl : FreeGroup.IsReduced (W ++ W) := by
    have := (h.flatten_replicate 2).isReduced
    simpa using this
  -- Any rotation of `W` occurs as a (contiguous) subword of `W ++ W`.
  have hinf : W.rotate n <:+: W ++ W := by
    rw [← List.rotate_mod W n]
    rw [List.rotate_eq_drop_append_take_mod]
    simp only [Nat.mod_mod]
    refine ⟨W.take (n % W.length), W.drop (n % W.length), ?_⟩
    have key : W ++ W =
        (W.take (n % W.length) ++ W.drop (n % W.length)) ++
          (W.take (n % W.length) ++ W.drop (n % W.length)) := by
      rw [List.take_append_drop]
    rw [key]
    simp only [List.append_assoc]
  exact hfl.infix hinf

end Work.OROneRel

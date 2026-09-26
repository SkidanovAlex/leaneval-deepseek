import Mathlib.GroupTheory.FreeGroup.Reduce

namespace Commons.GroupTheory.FreeGroup

lemma reduce_append_no_junction {α : Type*} [DecidableEq α] (X Y : List (α × Bool))
    (hX : FreeGroup.IsReduced X) (hY : FreeGroup.IsReduced Y)
    (h : ∀ a b, List.getLast? X = some (a, b) → List.head? Y = some (a, !b) → False) :
    FreeGroup.reduce (X ++ Y) = X ++ Y := by
  -- `X ++ Y` is reduced: `X` and `Y` are reduced, and the letters at the junction
  -- (`getLast? X`, `head? Y`) do not cancel by hypothesis `h`.
  have hXY : FreeGroup.IsReduced (X ++ Y) := by
    unfold FreeGroup.IsReduced
    refine List.IsChain.append (R := fun a b : α × Bool => a.1 = b.1 → a.2 = b.2) ?_ ?_ ?_
    · simpa [FreeGroup.IsReduced] using hX
    · simpa [FreeGroup.IsReduced] using hY
    · rintro ⟨a, b⟩ hx ⟨c, d⟩ hy h1
      change b = d
      by_contra hne
      have h1' : a = c := by simpa using h1
      have hx' : List.getLast? X = some (a, b) := by simpa using hx
      have hy' : List.head? Y = some (c, d) := by simpa using hy
      have hd : d = !b := by
        exact (Bool.eq_not_iff).mpr (Ne.symm hne)
      have hy'' : List.head? Y = some (a, !b) := by
        rw [hy']
        exact congrArg some (by
          rw [← h1', hd])
      exact h a b hx' hy''
  exact hXY.reduce_eq

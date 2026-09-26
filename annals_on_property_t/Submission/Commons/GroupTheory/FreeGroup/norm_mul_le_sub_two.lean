import Mathlib.GroupTheory.FreeGroup.Reduce

namespace Commons.GroupTheory.FreeGroup

/-- If the reduced word of `x` ends with the letter `(a, b)` and the reduced word
of `y` begins with the inverse letter `(a, ¬b)`, then those two letters cancel in
the product, so `‖x * y‖ ≤ ‖x‖ + ‖y‖ - 2`. -/
lemma norm_mul_le_sub_two {α : Type*} [DecidableEq α] (x y : FreeGroup α) (a : α) (b : Bool)
    (L M : List (α × Bool)) :
    FreeGroup.toWord x = L ++ [(a, b)] →
    FreeGroup.toWord y = (a, Bool.not b) :: M →
    FreeGroup.norm (x * y) ≤ FreeGroup.norm x + FreeGroup.norm y - 2 := by
  intro hx hy
  -- `x.toWord ++ y.toWord` contains the adjacent cancelling pair `(a, b) (a, ¬b)`,
  -- so it reduces in one step to `L ++ M`.
  have hword_red : FreeGroup.Red.Step (x.toWord ++ y.toWord) (L ++ M) := by
    rw [hx, hy]
    rw [List.append_assoc]
    exact (FreeGroup.Red.Step.not (L₁ := L) (L₂ := M) (x := a) (b := b))
  have hword : FreeGroup.reduce (x.toWord ++ y.toWord) = FreeGroup.reduce (L ++ M) :=
    FreeGroup.reduce.eq_of_red hword_red.to_red
  unfold FreeGroup.norm
  rw [FreeGroup.toWord_mul, hword]
  rw [hx, hy]
  calc
    (FreeGroup.reduce (L ++ M)).length ≤ (L ++ M).length :=
      FreeGroup.Red.length_le FreeGroup.reduce.red
    _ = L.length + M.length := by rw [List.length_append]
    _ = (L.length + 1) + (M.length + 1) - 2 := by omega
    _ = (L ++ [(a, b)]).length + ((a, Bool.not b) :: M).length - 2 := by
      simp [List.length_append, List.length_cons]

end Commons.GroupTheory.FreeGroup
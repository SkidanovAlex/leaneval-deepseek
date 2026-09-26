import Mathlib.GroupTheory.FreeGroup.Reduce

namespace Commons.GroupTheory.FreeGroup

/-- If `L ++ [(a, b)]` is a reduced word (so that its last letter `(a, b)` is not
cancellable), then appending the opposite letter `(a, !b)` and reducing cancels
exactly that last letter, leaving `L`. -/
private lemma reduce_append_cancel_last {α : Type*} [DecidableEq α] (L : List (α × Bool))
    (a : α) (b : Bool) (hL : FreeGroup.IsReduced (L ++ [(a, b)])) :
    FreeGroup.reduce ((L ++ [(a, b)]) ++ [(a, !b)]) = L := by
  have hstep0 : FreeGroup.Red.Step ([(a, b)] ++ [(a, !b)]) [] := by
    simp
  have hstep' : FreeGroup.Red.Step (L ++ ([(a, b)] ++ [(a, !b)])) L := by
    simpa using (FreeGroup.Red.Step.append_left (L₁ := L) hstep0)
  have hred : FreeGroup.Red (L ++ ([(a, b)] ++ [(a, !b)])) L := hstep'.to_red
  have hLred : FreeGroup.IsReduced L := FreeGroup.IsReduced.infix hL ⟨[], [(a, b)], by simp⟩
  calc
    FreeGroup.reduce ((L ++ [(a, b)]) ++ [(a, !b)]) =
        FreeGroup.reduce (L ++ ([(a, b)] ++ [(a, !b)])) := by
          rw [List.append_assoc]
    _ = FreeGroup.reduce L := FreeGroup.reduce.eq_of_red hred
    _ = L := FreeGroup.IsReduced.reduce_eq hLred

lemma norm_mul_cancel_last {α : Type*} [DecidableEq α] (x : FreeGroup α) (a : α) (b : Bool)
    (L : List (α × Bool)) :
    FreeGroup.toWord x = L ++ [(a, b)] →
    FreeGroup.norm (x * (if b then (FreeGroup.of a)⁻¹ else FreeGroup.of a)) = FreeGroup.norm x - 1 := by
  intro h
  cases b with
  | false =>
      -- The last letter `(a, false)` of `x.toWord` represents `(of a)⁻¹`, so
      -- right-multiplying by `of a` cancels exactly that letter.
      have hb : (if false = true then (FreeGroup.of a)⁻¹ else FreeGroup.of a) =
          FreeGroup.of a := by simp
      rw [hb]
      have hxw : FreeGroup.toWord (x * FreeGroup.of a) = L := by
        rw [FreeGroup.toWord_mul, h]
        simp only [FreeGroup.toWord_of]
        exact reduce_append_cancel_last L a false (by simpa [h] using FreeGroup.isReduced_toWord (x := x))
      rw [FreeGroup.norm, hxw]
      rw [FreeGroup.norm, h]
      simp
  | true =>
      -- The last letter `(a, true)` of `x.toWord` represents `of a`, so
      -- right-multiplying by `(of a)⁻¹` cancels exactly that letter.
      have hb : (if true = true then (FreeGroup.of a)⁻¹ else FreeGroup.of a) =
          (FreeGroup.of a)⁻¹ := by simp
      rw [hb]
      have hxw : FreeGroup.toWord (x * (FreeGroup.of a)⁻¹) = L := by
        rw [FreeGroup.toWord_mul, h]
        simp only [FreeGroup.toWord_inv, FreeGroup.toWord_of]
        simpa [FreeGroup.invRev] using (reduce_append_cancel_last L a true
          (by simpa [h] using FreeGroup.isReduced_toWord (x := x)))
      rw [FreeGroup.norm, hxw]
      rw [FreeGroup.norm, h]
      simp

end Commons.GroupTheory.FreeGroup

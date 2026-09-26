import Mathlib.GroupTheory.FreeGroup.Reduce

namespace Commons.GroupTheory.FreeGroup

/-- If `(a, b) :: M` is a reduced word, then prepending the inverse letter `(a, !b)`
and reducing cancels exactly the first letter, leaving `M`. -/
private lemma reduce_append_cancel_head {α : Type*} [DecidableEq α] (a : α) (b : Bool)
    (M : List (α × Bool)) (hM : FreeGroup.IsReduced ((a, b) :: M)) :
    FreeGroup.reduce ([(a, !b)] ++ ((a, b) :: M)) = M := by
  have hstep : FreeGroup.Red.Step ((a, !b) :: (a, b) :: M) M := by
    exact FreeGroup.Red.Step.cons_not_rev (L := M) (x := a) (b := b)
  have hred : FreeGroup.Red ([(a, !b)] ++ ((a, b) :: M)) M := by
    simpa using hstep.to_red
  have hMred : FreeGroup.IsReduced M := by
    unfold FreeGroup.IsReduced
    exact List.IsChain.suffix hM ⟨[(a, b)], by simp⟩
  calc
    FreeGroup.reduce ([(a, !b)] ++ ((a, b) :: M)) = FreeGroup.reduce M := by
      exact FreeGroup.reduce.eq_of_red hred
    _ = M := FreeGroup.IsReduced.reduce_eq hMred

lemma norm_mul_cancel_head {α : Type*} [DecidableEq α] (x : FreeGroup α) (a : α) (b : Bool)
    (M : List (α × Bool)) :
    FreeGroup.toWord x = (a, b) :: M →
    FreeGroup.norm ((if b then (FreeGroup.of a)⁻¹ else FreeGroup.of a) * x) =
      FreeGroup.norm x - 1 := by
  intro h
  cases b with
  | false =>
      -- The first letter `(a, false)` represents `(of a)⁻¹`; left-multiplying by
      -- `of a` cancels exactly that letter.
      have hb : (if false = true then (FreeGroup.of a)⁻¹ else FreeGroup.of a) =
          FreeGroup.of a := by simp
      rw [hb]
      have hxw : FreeGroup.toWord (FreeGroup.of a * x) = M := by
        rw [FreeGroup.toWord_mul, h]
        simp only [FreeGroup.toWord_of]
        exact reduce_append_cancel_head a false M (by simpa [h] using FreeGroup.isReduced_toWord (x := x))
      rw [FreeGroup.norm, hxw]
      rw [FreeGroup.norm, h]
      simp
  | true =>
      -- The first letter `(a, true)` represents `of a`; left-multiplying by
      -- `(of a)⁻¹` cancels exactly that letter.
      have hb : (if true = true then (FreeGroup.of a)⁻¹ else FreeGroup.of a) =
          (FreeGroup.of a)⁻¹ := by simp
      rw [hb]
      have hxw : FreeGroup.toWord ((FreeGroup.of a)⁻¹ * x) = M := by
        rw [FreeGroup.toWord_mul, h]
        simp only [FreeGroup.toWord_inv, FreeGroup.toWord_of, FreeGroup.invRev]
        exact reduce_append_cancel_head a true M (by simpa [h] using FreeGroup.isReduced_toWord (x := x))
      rw [FreeGroup.norm, hxw]
      rw [FreeGroup.norm, h]
      simp

end Commons.GroupTheory.FreeGroup

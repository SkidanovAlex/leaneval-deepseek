import Mathlib.GroupTheory.FreeGroup.Reduce

namespace Commons.GroupTheory.FreeGroup

lemma reduce_concat_length_cancel_middle {α : Type*} [DecidableEq α]
    (X C Z : List (α × Bool)) (hC : FreeGroup.reduce C = []) :
    (FreeGroup.reduce (X ++ C ++ Z)).length ≤ X.length + Z.length := by
  have hC1 : (FreeGroup.mk C : FreeGroup α) = 1 := by
    have hC0 : (FreeGroup.mk C).toWord = [] := by
      simpa [FreeGroup.toWord_mk] using hC
    exact FreeGroup.toWord_eq_nil_iff.mp hC0
  have hmk : (FreeGroup.mk (X ++ C ++ Z) : FreeGroup α) = FreeGroup.mk (X ++ Z) := by
    rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
    rw [hC1]
    simp
  calc
    (FreeGroup.reduce (X ++ C ++ Z)).length = (FreeGroup.reduce (X ++ Z)).length := by
      rw [FreeGroup.reduce.sound hmk]
    _ ≤ (X ++ Z).length := FreeGroup.reduce.red.length_le
    _ = X.length + Z.length := by simp

end Commons.GroupTheory.FreeGroup
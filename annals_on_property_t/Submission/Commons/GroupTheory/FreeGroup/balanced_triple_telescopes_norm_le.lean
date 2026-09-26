import Mathlib.GroupTheory.FreeGroup.Reduce
import Submission.Commons.GroupTheory.FreeGroup.reduce_concat_length_cancel_middle
import Submission.Commons.GroupTheory.FreeGroup.reduce_append_invRev_right
import Submission.Commons.GroupTheory.FreeGroup.reduce_append_reduce

namespace Commons.GroupTheory.FreeGroup

lemma balanced_triple_telescopes_norm_le {α : Type*} [DecidableEq α]
    (X A B Z : List (α × Bool)) :
    FreeGroup.norm (((FreeGroup.mk (X ++ FreeGroup.invRev A)) * (FreeGroup.mk (A ++ B))) *
      (FreeGroup.mk (FreeGroup.invRev B ++ Z))) ≤ X.length + Z.length := by
  let C : List (α × Bool) := FreeGroup.invRev A ++ A ++ B ++ FreeGroup.invRev B
  -- The middle block `C` reduces to the empty word: `invRev A ++ A` and `B ++ invRev B`
  -- each fully cancel.
  have hC0 : FreeGroup.reduce C = [] := by
    dsimp [C]
    rw [show FreeGroup.invRev A ++ A ++ B ++ FreeGroup.invRev B =
        (FreeGroup.invRev A ++ A) ++ (B ++ FreeGroup.invRev B) by rw [List.append_assoc]]
    rw [FreeGroup.reduce_append_reduce]
    rw [FreeGroup.reduce_invRev_left_cancel]
    rw [reduce_append_invRev_right]
    simp
  -- The product telescopes into the single word `X ++ C ++ Z`.
  have hprod : ((FreeGroup.mk (X ++ FreeGroup.invRev A)) * (FreeGroup.mk (A ++ B))) *
      (FreeGroup.mk (FreeGroup.invRev B ++ Z)) =
      FreeGroup.mk (X ++ C ++ Z) := by
    dsimp [C]
    simp [List.append_assoc]
  rw [hprod]
  rw [FreeGroup.norm, FreeGroup.toWord_mk]
  exact reduce_concat_length_cancel_middle X C Z hC0

end Commons.GroupTheory.FreeGroup

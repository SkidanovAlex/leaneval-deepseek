/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# `gxTrivFrom` is additive under multiplication of the free group

`gxTrivFrom c D i L` says that every traversal of the walk of `L` read from the level `i`
(`decor c i L`) uses an edge of the `ℤ`-cover whose loop class under the gauge `D` is trivial.

The point of the lemma below is that the walk of a *product* is the concatenation of the two walks
followed by a free reduction.  Two facts are combined:

* `decor_append`: the decoration of `L₁ ++ L₂` read from `i` is the decoration of `L₁` read from `i`
  followed by the decoration of `L₂` read from `i + lsig c L₁` (`Submission.Work.OROneRel.decor_pow_flatMap`);
* `decor_sublist_of_red`: free reduction only *deletes* decorated letters, the running level being
  restored after every cancelling pair (`Submission.Work.OROneRel.decor_winE_of_red`).

So `decor c i (wordOf (A * B))` is a sublist of
`decor c i (wordOf A) ++ decor c (i + lsig c (wordOf A)) (wordOf B)`, and a condition on the edges
of the decorated letters transfers from the longer word to the shorter one.
-/

import Mathlib
import Submission.Work.OROneRel.gaugeExtWindowDefs
import Submission.Work.OROneRel.decor_pow_flatMap
import Submission.Work.OROneRel.decor_winE_of_red

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **The product of reduced words reduces to the reduced word of the product**:
`wordOf A ++ wordOf B` reduces to `wordOf (A * B)` in the free-reduction sense of
`FreeGroup.Red`. -/
theorem gxRed_wordOf_mul (A B : FreeGroup α) :
    FreeGroup.Red (wordOf A ++ wordOf B) (wordOf (A * B)) := by
  classical
  have h0 : FreeGroup.mk (wordOf A) * FreeGroup.mk (wordOf B) =
      FreeGroup.mk (wordOf (A * B)) := by
    rw [mk_wordOf, mk_wordOf, mk_wordOf]
  have h : FreeGroup.mk (wordOf A ++ wordOf B) = FreeGroup.mk (wordOf (A * B)) := by
    rw [← FreeGroup.mul_mk]; exact h0
  have h1 := FreeGroup.reduce.red (L := wordOf A ++ wordOf B)
  have h2 : FreeGroup.reduce (wordOf A ++ wordOf B) = wordOf (A * B) := by
    have h3 := FreeGroup.reduce.sound h
    have h4 : FreeGroup.reduce (wordOf (A * B)) = wordOf (A * B) := by
      rw [wordOf]
      exact FreeGroup.reduce_toWord (A * B)
    rwa [h4] at h3
  rwa [h2] at h1

theorem gxTrivFrom_mul {α : Type*} [DecidableEq α] (c : α → ℤ) (D : ℤ → FreeGroup α) (i : ℤ)
    (A B : FreeGroup α)
    (hA : Work.OROneRel.gxTrivFrom c D i (Work.OROneRel.wordOf A))
    (hB : Work.OROneRel.gxTrivFrom c D (i + Work.OROneRel.lsig c (Work.OROneRel.wordOf A))
      (Work.OROneRel.wordOf B)) :
    Work.OROneRel.gxTrivFrom c D i (Work.OROneRel.wordOf (A * B)) := by
  intro p hp
  have hsub := decor_sublist_of_red c i (gxRed_wordOf_mul A B)
  have hp' : p ∈ decor c i (wordOf A ++ wordOf B) := List.Sublist.mem hp hsub
  rw [decor_append] at hp'
  rcases List.mem_append.mp hp' with h | h
  · exact hA p h
  · exact hB p h

end Work.OROneRel

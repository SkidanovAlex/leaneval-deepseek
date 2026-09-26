import Submission.Work.NielsenPeel
import Submission.Work.T3Rebalance

open Submission.Nielsen
open Commons.GroupTheory.FreeGroup
open FreeGroup
set_option autoImplicit false

/-!
# Item 3, ClassStability: a combined coordinate leaves the pass classes

The balanced-phase fixpoint at `p` (halves `A ++ B`, `|A| = |B|`; see
`FallTwoRunNotes.md` for the validated run semantics) repeatedly combines
every `q ≠ p` whose word ends with `B` (ends-move, new word
`Y ++ invRev A`) or begins with `B⁻¹` = `invRev B` (begins-move, new word
`A ++ Y`).  For the phase to be bounded one needs that a combined coordinate
never re-enters the class it just left.  This module proves the two word
facts at the root of that stability:

* `invRev_ne_of_reduced_append`: if `A ++ B` is reduced and `A` nonempty then
  `invRev A ≠ B` — `A ++ invRev A` telescopes to the empty word
  (`reduce_append_invRev_self`) but is already reduced, so it cannot equal
  the reduced `A ++ B`; the mirror `A_ne_invRev_of_reduced_append`
  (`A ≠ invRev B`).
* `not_ends_B_of_ends_replace`: after a no-cancellation ends-move the new
  word `Y ++ invRev A` does **not** end with `B` (an ends-with-`B` suffix
  `Y' ++ B` equal to it would have `|Y'| = |Y|` by equal lengths and then
  `invRev A = B` by left-cancelling the equal-length prefixes).
* `not_begins_invRevB_of_begins_replace`: after a no-cancellation begins-move
  the new word `A ++ Y` does **not** begin with `B⁻¹` (mirror via
  `take`-cancellation).

(Class stability alone gives each coordinate at most one ends-move and one
begins-move *per pass round*; the interaction between the two classes —
whether a begins-move can create a fresh ends-with-`B` member — is subtler
and is part of the still-open phase-termination analysis recorded in
`FallTwoRunNotes.md`; nothing here claims more than the two word facts.)

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- If `A ++ B` is reduced and `A` is nonempty, then `invRev A ≠ B`
(`A ++ invRev A` would telescope to the empty word but is already reduced). -/
lemma invRev_ne_of_reduced_append {α : Type*} [DecidableEq α]
    (A B : List (α × Bool)) (hA : A ≠ [])
    (hred : FreeGroup.IsReduced (A ++ B)) : FreeGroup.invRev A ≠ B := by
  intro h
  have h2 : A ++ B = A ++ FreeGroup.invRev A := by rw [h]
  have hred' : FreeGroup.IsReduced (A ++ FreeGroup.invRev A) := by simpa [h2] using hred
  have hred2 : FreeGroup.reduce (A ++ FreeGroup.invRev A) = A ++ FreeGroup.invRev A :=
    FreeGroup.isReduced_iff_reduce_eq.mp hred'
  have hred3 : FreeGroup.reduce (A ++ FreeGroup.invRev A) = ([] : List (α × Bool)) :=
    reduce_append_invRev_self A
  have hnil : A ++ FreeGroup.invRev A = ([] : List (α × Bool)) := by
    rw [← hred2, hred3]
  have hlen : (A ++ FreeGroup.invRev A).length = 0 := by
    rw [hnil]
    rfl
  rw [List.length_append, FreeGroup.invRev_length] at hlen
  have hA0 : A.length = 0 := by omega
  cases A with
  | nil => exact hA rfl
  | cons x xs =>
      simp at hA0

/-- Mirror: with `A` nonempty and `A ++ B` reduced, `A ≠ invRev B`. -/
lemma A_ne_invRev_of_reduced_append {α : Type*} [DecidableEq α]
    (A B : List (α × Bool)) (hA : A ≠ [])
    (hred : FreeGroup.IsReduced (A ++ B)) : A ≠ FreeGroup.invRev B := by
  intro h
  apply_fun FreeGroup.invRev at h
  have h' : FreeGroup.invRev A = B := by simpa [FreeGroup.invRev_invRev] using h
  exact invRev_ne_of_reduced_append A B hA hred h'

/-- After a (no-cancellation) ends-move the coordinate's word `Y ++ invRev A`
does not end with `B` (halves `|A| = |B|`, `A ++ B` reduced, `A` nonempty). -/
lemma not_ends_B_of_ends_replace {α : Type*} [DecidableEq α]
    (Y A B : List (α × Bool)) (hA : A ≠ []) (hAB : A.length = B.length)
    (hred : FreeGroup.IsReduced (A ++ B)) :
    ¬ ∃ Y' : List (α × Bool), Y ++ FreeGroup.invRev A = Y' ++ B := by
  rintro ⟨Y', hEq⟩
  have hlen := congrArg List.length hEq
  rw [List.length_append, List.length_append, FreeGroup.invRev_length] at hlen
  have hY' : Y'.length = Y.length := by omega
  have hdrop := congrArg (fun w : List (α × Bool) => w.drop Y.length) hEq
  have hd1 : (Y ++ FreeGroup.invRev A).drop Y.length = FreeGroup.invRev A := by
    simp
  have hd2 : (Y' ++ B).drop Y.length = B := by
    rw [← hY']
    simp
  rw [hd1, hd2] at hdrop
  exact invRev_ne_of_reduced_append A B hA hred hdrop

/-- After a (no-cancellation) begins-move the coordinate's word `A ++ Y` does
not begin with `B⁻¹` (`invRev B`): halves `|A| = |B|`, reduced, `A` nonempty. -/
lemma not_begins_invRevB_of_begins_replace {α : Type*} [DecidableEq α]
    (A B Y : List (α × Bool)) (hA : A ≠ []) (hAB : A.length = B.length)
    (hred : FreeGroup.IsReduced (A ++ B)) :
    ¬ ∃ Y' : List (α × Bool), A ++ Y = FreeGroup.invRev B ++ Y' := by
  rintro ⟨Y', hEq⟩
  have hlen := congrArg List.length hEq
  rw [List.length_append, List.length_append, FreeGroup.invRev_length] at hlen
  have hY' : Y'.length = Y.length := by omega
  have htake := congrArg (fun w : List (α × Bool) => w.take A.length) hEq
  have ht1 : (A ++ Y).take A.length = A := by simp
  have ht2 : (FreeGroup.invRev B ++ Y').take A.length = FreeGroup.invRev B := by
    have hb : A.length = (FreeGroup.invRev B).length := by
      rw [FreeGroup.invRev_length, hAB]
    rw [hb]
    simp
  rw [ht1, ht2] at htake
  exact (A_ne_invRev_of_reduced_append A B hA hred) htake

end Submission.Nielsen

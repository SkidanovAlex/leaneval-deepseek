import Submission.Work.Item3.PassRound
import Submission.Work.Item3.PassLengths
import Submission.Work.Item3.ClassStability
import Submission.Work.NielsenPeel

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
open scoped BigOperators
set_option autoImplicit false

/-!
# Item 3, PassDynamics: what one round does to each coordinate

With the round product `passRound` (PassRound.lean) in hand, this module
records the *per-coordinate dynamics* of one canonical round at the balanced
coordinate `c` (halves `A ++ B`, `|A| = |B|`), in the no-cancellation
(no-strict-move) regime — the regime in which the classical balanced phase
operates (any boundary cancellation would be a strict move, closing the
Fall-II pin immediately via `FallII.fallII_*_strict` /
`PassRound.passIter_then_strict`):

* `passRound_coord_word_end` / `passRound_coord_word_begin`: an active
  coordinate's new word is exactly `Y ++ invRev A` (ends-with-`B` class) resp.
  `A ++ Y` (begins-with-`B⁻¹` class), with no boundary cancellation
  (`align Y (invRev A) = 0` resp. `align A Y = 0`) — the `B`-suffix is
  replaced by `invRev A`, the `B⁻¹`-prefix by `A`;
* `passRound_coord_not_ends` / `passRound_coord_not_begins`: an active
  coordinate **leaves the class it was combined from**: after the round its
  word no longer ends with `B` resp. no longer begins with `B⁻¹`
  (`ClassStability` word facts: `invRev A ≠ B` and `A ≠ invRev B` for the
  reduced nonempty halves);
* `passRound_coord_unchanged`: a coordinate in neither class is unchanged by
  the round (`item2` is the identity there).

Together these give the phase-dynamics invariant consumed by the
phase-termination and no-reappearance arguments: a coordinate's word changes
only in rounds where it is active; after its ends-move it never ends with `B`
again, after its begins-move never begins with `B⁻¹` again (its tail resp.
head is invariant under later moves of the other class, which multiply on the
left resp. right) — so each coordinate is combined at most once per class per
phase.  The no-reappearance/balancedness statement (the next step, recorded in
`FallTwoRunNotes.md` and `Status.lean`) is a separate global claim about the
new automorphism's aggregates and is NOT claimed here.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/



namespace Submission.Nielsen

/-- An ends-with-`B` coordinate (`q ≠ c`, word `Y ++ B`) whose round move has
no boundary cancellation gets the explicit new word `Y ++ invRev A` after one
round. -/
lemma passRound_coord_word_end {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (c q : Fin n) (A B : List (Fin n × Bool)) (hqc : q ≠ c)
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B)
    (Y : List (Fin n × Bool)) (hqE : (α (FreeGroup.of q)).toWord = Y ++ B)
    (h0 : align Y (FreeGroup.invRev A) = 0) :
    ((α * passRound α c A B) (FreeGroup.of q)).toWord =
      Y ++ FreeGroup.invRev A := by
  unfold passRound
  have happ := item2Pass_apply_ends α c A B (passQ c) (passQ_nodup c)
    (passQ_mem.mpr hqc) hqc (passQ_not_mem_c c) (by exact ⟨Y, hqE⟩)
  have hw : ((α * item2Pass α c A B (passQ c)) (FreeGroup.of q)).toWord =
      FreeGroup.reduce (Y ++ FreeGroup.invRev A) := by
    rw [happ]
    rw [FreeGroup.toWord_mul, FreeGroup.toWord_inv]
    rw [hqE, hmid]
    rw [FreeGroup.invRev_append]
    exact rebalance_join_reduce A B Y
  rw [hw]
  have hwred : FreeGroup.IsReduced ((α (FreeGroup.of q)).toWord) :=
    FreeGroup.isReduced_toWord (x := α (FreeGroup.of q))
  have hY : FreeGroup.IsReduced Y := by
    rw [hqE] at hwred
    have h' := isReduced_take (Y ++ B) Y.length hwred
    simpa using h'
  have hwredc : FreeGroup.IsReduced ((α (FreeGroup.of c)).toWord) :=
    FreeGroup.isReduced_toWord (x := α (FreeGroup.of c))
  have hA : FreeGroup.IsReduced A := by
    rw [hmid] at hwredc
    have h' := isReduced_take (A ++ B) A.length hwredc
    simpa using h'
  exact reduce_no_cancel_of_align_zero Y (FreeGroup.invRev A) hY
    (reduced_invRev A hA) h0

/-- A begins-with-`B⁻¹` coordinate (`q ≠ c`, word `invRev B ++ Y`, not ending
with `B`) whose round move has no boundary cancellation gets the explicit new
word `A ++ Y` after one round. -/
lemma passRound_coord_word_begin {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (c q : Fin n) (A B : List (Fin n × Bool)) (hqc : q ≠ c)
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B)
    (hnoE : ¬ ∃ Y : List (Fin n × Bool), (α (FreeGroup.of q)).toWord = Y ++ B)
    (Y : List (Fin n × Bool)) (hqB : (α (FreeGroup.of q)).toWord = FreeGroup.invRev B ++ Y)
    (h0 : align A Y = 0) :
    ((α * passRound α c A B) (FreeGroup.of q)).toWord = A ++ Y := by
  unfold passRound
  have happ := item2Pass_apply_begins α c A B (passQ c) (passQ_nodup c)
    (passQ_mem.mpr hqc) hqc (passQ_not_mem_c c) hnoE (by exact ⟨Y, hqB⟩)
  have hw : ((α * item2Pass α c A B (passQ c)) (FreeGroup.of q)).toWord =
      FreeGroup.reduce (A ++ Y) := by
    rw [happ]
    rw [FreeGroup.toWord_mul]
    rw [hmid, hqB]
    rw [show (A ++ B) ++ (FreeGroup.invRev B ++ Y) =
        A ++ ((B ++ FreeGroup.invRev B) ++ Y) by simp [List.append_assoc]]
    rw [reduce_middle_empty (X := A) (M := B ++ FreeGroup.invRev B) (Z := Y)
      (reduce_append_invRev_self B)]
  rw [hw]
  have hwred : FreeGroup.IsReduced ((α (FreeGroup.of q)).toWord) :=
    FreeGroup.isReduced_toWord (x := α (FreeGroup.of q))
  have hY : FreeGroup.IsReduced Y := by
    rw [hqB] at hwred
    have h' := isReduced_drop (FreeGroup.invRev B ++ Y) (FreeGroup.invRev B).length hwred
    simpa using h'
  have hwredc : FreeGroup.IsReduced ((α (FreeGroup.of c)).toWord) :=
    FreeGroup.isReduced_toWord (x := α (FreeGroup.of c))
  have hA : FreeGroup.IsReduced A := by
    rw [hmid] at hwredc
    have h' := isReduced_take (A ++ B) A.length hwredc
    simpa using h'
  exact reduce_no_cancel_of_align_zero A Y hA hY h0

/-- After one non-strict round an ends-with-`B` coordinate no longer ends with
`B`. -/
theorem passRound_coord_not_ends {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (c q : Fin n) (A B : List (Fin n × Bool)) (hqc : q ≠ c)
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B) (hAB : A.length = B.length)
    (hA : A ≠ [])
    (Y : List (Fin n × Bool)) (hqE : (α (FreeGroup.of q)).toWord = Y ++ B)
    (h0 : align Y (FreeGroup.invRev A) = 0) :
    ¬ ∃ Y' : List (Fin n × Bool),
      ((α * passRound α c A B) (FreeGroup.of q)).toWord = Y' ++ B := by
  have hw := passRound_coord_word_end α c q A B hqc hmid Y hqE h0
  rw [hw]
  have hwredc : FreeGroup.IsReduced ((α (FreeGroup.of c)).toWord) :=
    FreeGroup.isReduced_toWord (x := α (FreeGroup.of c))
  have hred : FreeGroup.IsReduced (A ++ B) := by
    rw [hmid] at hwredc
    exact hwredc
  exact not_ends_B_of_ends_replace Y A B hA hAB hred

/-- After one non-strict round a begins-with-`B⁻¹` coordinate no longer begins
with `B⁻¹`. -/
theorem passRound_coord_not_begins {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (c q : Fin n) (A B : List (Fin n × Bool)) (hqc : q ≠ c)
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B) (hAB : A.length = B.length)
    (hA : A ≠ [])
    (hnoE : ¬ ∃ Y : List (Fin n × Bool), (α (FreeGroup.of q)).toWord = Y ++ B)
    (Y : List (Fin n × Bool)) (hqB : (α (FreeGroup.of q)).toWord = FreeGroup.invRev B ++ Y)
    (h0 : align A Y = 0) :
    ¬ ∃ Y' : List (Fin n × Bool),
      ((α * passRound α c A B) (FreeGroup.of q)).toWord = FreeGroup.invRev B ++ Y' := by
  have hw := passRound_coord_word_begin α c q A B hqc hmid hnoE Y hqB h0
  rw [hw]
  have hwredc : FreeGroup.IsReduced ((α (FreeGroup.of c)).toWord) :=
    FreeGroup.isReduced_toWord (x := α (FreeGroup.of c))
  have hred : FreeGroup.IsReduced (A ++ B) := by
    rw [hmid] at hwredc
    exact hwredc
  exact not_begins_invRevB_of_begins_replace A B Y hA hAB hred

/-- A coordinate that is in neither pass class is unchanged by the round. -/
theorem passRound_coord_unchanged {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (c q : Fin n) (A B : List (Fin n × Bool)) (hqc : q ≠ c)
    (hnoE : ¬ ∃ Y : List (Fin n × Bool), (α (FreeGroup.of q)).toWord = Y ++ B)
    (hnoB : ¬ ∃ Y : List (Fin n × Bool),
      (α (FreeGroup.of q)).toWord = FreeGroup.invRev B ++ Y) :
    (α * passRound α c A B) (FreeGroup.of q) = α (FreeGroup.of q) := by
  unfold passRound
  have hid : item2 α c q A B = 1 :=
    item2_eq_one_of_neither α c q A B hqc hnoE hnoB
  exact pass_coord_unchanged_of_id α c q A B (passQ c) (passQ_nodup c)
    (passQ_mem.mpr hqc) hid

end Submission.Nielsen

import Submission.Work.Item3.PassRound
import Submission.Work.Item3.PassDynamics
import Submission.Work.Item3.WitnessCover

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
open scoped BigOperators
set_option autoImplicit false

/-!
# Item 3, PostRoundSupport: the round-level covering bound (CoverBound at any row index)

The `i < p` case of no-reappearance consumes the `CoverBound` content about a
hypothetical surviving witness at a row position `i <= p` — the element and
its two covering neighbours.  This module assembles that content at the
*round* level, for **every** coordinate:

    passRound_coord_letters_old_or_new (c balanced, word A ++ B) : every
        letter of toWord((α·round)(a_q)) is a letter of the OLD word
        toWord(α(a_q)) or lies in newLetterSet A
        -- ends-active: item2Pass_apply_ends + rebalance_join_reduce
        --   (new word reduce(Y ++ invRev A), letters in Y or newLetterSet A,
        --   CoverBound.replace_suffix_new_letters) — WitnessCover's
        --   pass_ends_coord_new_letters;
        -- begins-active: mirror (pass_begins_coord_new_letters);
        -- inert: unchanged (PassDynamics.passRound_coord_unchanged);
        -- balanced coordinate: unchanged (item2Pass_fix)

No no-cancellation hypothesis is needed: cancellations only remove letters, so
the support claim holds for every round regardless of strictness.  Applied to
a row position `i <= p` and to any two other coordinates, this gives: every
genuinely-new letter of the witness triple lies in `newLetterSet A`
(`|newLetterSet A| <= 2|A|`, CoverBound) — the covering-bound premise of the
`i < p` no-reappearance argument.

**What this module does not claim:** the contradiction itself.  Machine data
(`FallTwoRunNotes.md`) shows low-row elements ARE combined by the pass (52 of
290 residual phases), so the `i < p` case genuinely involves changed low
words, and containment of new letters in `newLetterSet A` is not by itself
contradictory — the global mechanism remains the open core.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/



namespace Submission.Nielsen

/-- **Round-level covering bound, every coordinate.**  After one canonical
round at the balanced coordinate `c` (word `A ++ B`), every letter of every
coordinate's post-round word is either a letter of its OLD word (before the
round) or lies in the new-letter set `newLetterSet A` (the letters of the
balanced first half and their inverses, `|newLetterSet A| <= 2|A|`).  No
no-cancellation hypothesis is needed: cancellations only remove letters.  This
is the `CoverBound` instance at the *round* level, valid for every coordinate
— in particular for the element at any row position `i <= p` and for the two
neighbour coordinates of a hypothetical surviving witness there. -/
theorem passRound_coord_letters_old_or_new {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (c q : Fin n) (A B : List (Fin n × Bool))
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B) :
    ∀ l ∈ ((α * passRound α c A B) (FreeGroup.of q)).toWord,
      l ∈ (α (FreeGroup.of q)).toWord ∨ l ∈ newLetterSet A := by
  classical
  unfold passRound
  by_cases hqc : q = c
  · subst q
    intro l hl
    left
    have hfix : (α * item2Pass α c A B (passQ c)) (FreeGroup.of c) = α (FreeGroup.of c) :=
      item2Pass_fix α c A B (passQ c) (passQ_not_mem_c c)
    rw [hfix] at hl
    exact hl
  · by_cases hE : ∃ Y : List (Fin n × Bool), (α (FreeGroup.of q)).toWord = Y ++ B
    · exact pass_ends_coord_new_letters α c q A B (passQ c) (passQ_nodup c)
        (passQ_mem.mpr hqc) hqc (passQ_not_mem_c c) hmid hE
    · by_cases hB : ∃ Y : List (Fin n × Bool),
          (α (FreeGroup.of q)).toWord = FreeGroup.invRev B ++ Y
      · exact pass_begins_coord_new_letters α c q A B (passQ c) (passQ_nodup c)
          (passQ_mem.mpr hqc) hqc (passQ_not_mem_c c) hmid hE hB
      · -- neither: the coordinate is unchanged
        have hunch : (α * item2Pass α c A B (passQ c)) (FreeGroup.of q) =
            α (FreeGroup.of q) := by
          simpa [passRound] using (passRound_coord_unchanged α c q A B hqc hE hB)
        intro l hl
        left
        rw [hunch] at hl
        exact hl

end Submission.Nielsen

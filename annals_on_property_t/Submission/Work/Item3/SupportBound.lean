import Submission.Work.NielsenPeel

open Submission.Nielsen
open Commons.GroupTheory.FreeGroup
open FreeGroup
set_option autoImplicit false

/-!
# Item 3, SupportBound: the "Anfangs- und Endbestandteile bis A_p" bound

The surviving-witness obligation of `Item3/NoReappearance.lean` (a witness at
row position `i ≤ p` in the post-pass state would be an *entirely new
aggregate*) needs the word-level content of Nielsen 1919 p. 271: for the
elements that matter at positions `≤ p` — whose reduced length is at most
`|α_p| = 2·|A|` — half-absorption only involves initial/terminal segments of
length at most `|A|`, and after the item-2 pass such segments have not gained
anything that was not already in `α_p` ("solche sind keine neu entstanden,
die nicht schon in α_p vertreten waren").  This module transcribes that bound
at the word level.

The item-2 pass replaces, in an affected word, the `B`-suffix by `invRev A`
(ends-with-`B` elements) or the `B⁻¹`-prefix by `A` (begins-with-`B⁻¹`
elements), with `|A| = |B|`.  The exact reduction shape
(`NielsenPeel.two_word_reduction_shape`) gives, in the suffix case,

    reduce (Y ++ invRev A) = Y.take (|Y| − a) ++ (invRev A).drop a,
        a := align Y (invRev A) ≤ |A|,

i.e. the new word is an *unchanged head* of `Y` of length at least
`|Y| − |A|` followed by at most `|A|` letters drawn from `invRev A`
(`replace_suffix_shape`, `replace_suffix_head`, `replace_suffix_new_bound`);
the prefix case is the mirror (`replace_prefix_shape`).  Hence all *new*
boundary content any potential witness at `i ≤ p` could be built from is
bounded by `|A|` letters of the balanced first half (or its inverse) — the
transcription of the classical bound, whose base cases are proven here.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- `invRev` of a reduced word is reduced. -/
lemma reduced_invRev {α : Type*} [DecidableEq α] (L : List (α × Bool))
    (hL : FreeGroup.IsReduced L) : FreeGroup.IsReduced (FreeGroup.invRev L) :=
  FreeGroup.IsReduced.of_reduce_eq (by
    rw [FreeGroup.reduce_invRev]
    rw [FreeGroup.isReduced_iff_reduce_eq.mp hL])

/-- **Support-bound, base case (suffix replacement).**  Replacing the
`B`-suffix of a reduced word `Y ++ B` by `invRev A` (the item-2 move on an
ends-with-`B` element) yields exactly
`Y.take (|Y| − a) ++ (invRev A).drop a` with `a = align Y (invRev A) ≤ |A|`:
an unchanged head of `Y` of length at least `|Y| − |A|`, then at most `|A|`
letters drawn from `invRev A`. -/
theorem replace_suffix_shape {α : Type*} [DecidableEq α] (Y A : List (α × Bool))
    (hY : FreeGroup.IsReduced Y) (hA : FreeGroup.IsReduced A) :
    FreeGroup.reduce (Y ++ FreeGroup.invRev A) =
      Y.take (Y.length - align Y (FreeGroup.invRev A)) ++
        (FreeGroup.invRev A).drop (align Y (FreeGroup.invRev A)) := by
  exact two_word_reduction_shape Y (FreeGroup.invRev A) hY (reduced_invRev A hA)

/-- The head of the replacement of length `|Y| − a` is the unchanged head of
`Y`: no new content appears before that point. -/
theorem replace_suffix_head {α : Type*} [DecidableEq α] (Y A : List (α × Bool))
    (hY : FreeGroup.IsReduced Y) (hA : FreeGroup.IsReduced A) :
    (FreeGroup.reduce (Y ++ FreeGroup.invRev A)).take
        (Y.length - align Y (FreeGroup.invRev A)) =
      Y.take (Y.length - align Y (FreeGroup.invRev A)) := by
  rw [replace_suffix_shape Y A hY hA]
  rw [List.take_append_of_le_length (l₁ := Y.take (Y.length - align Y (FreeGroup.invRev A)))
    (l₂ := (FreeGroup.invRev A).drop (align Y (FreeGroup.invRev A)))
    (i := Y.length - align Y (FreeGroup.invRev A)) (by simp)]
  simp

/-- The new content at the seam is at most `|A|` letters, drawn from
`invRev A`. -/
theorem replace_suffix_new_bound {α : Type*} [DecidableEq α] (Y A : List (α × Bool))
    (hY : FreeGroup.IsReduced Y) (hA : FreeGroup.IsReduced A) :
    ((FreeGroup.reduce (Y ++ FreeGroup.invRev A)).drop
        (Y.length - align Y (FreeGroup.invRev A))).length ≤ A.length := by
  rw [replace_suffix_shape Y A hY hA]
  rw [List.drop_append_of_le_length (l₁ := Y.take (Y.length - align Y (FreeGroup.invRev A)))
    (l₂ := (FreeGroup.invRev A).drop (align Y (FreeGroup.invRev A)))
    (i := Y.length - align Y (FreeGroup.invRev A)) (by simp)]
  simp [List.length_drop, FreeGroup.invRev_length]

/-- **Support-bound, base case (prefix replacement).**  Mirror: replacing the
`B⁻¹`-prefix of a reduced word `invRev B ++ Y` by `A` (the item-2 move on a
begins-with-`B⁻¹` element) yields exactly
`A.take (|A| − a') ++ Y.drop a'` with `a' = align A Y ≤ |A|`: at most `|A|`
letters of new content from `A`, then an unchanged tail of `Y` of length at
least `|Y| − |A|`. -/
theorem replace_prefix_shape {α : Type*} [DecidableEq α] (A Y : List (α × Bool))
    (hA : FreeGroup.IsReduced A) (hY : FreeGroup.IsReduced Y) :
    FreeGroup.reduce (A ++ Y) =
      A.take (A.length - align A Y) ++ Y.drop (align A Y) := by
  exact two_word_reduction_shape A Y hA hY

end Submission.Nielsen

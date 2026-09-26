import Submission.Work.ShortImagesSigned

open Submission.Nielsen
open Commons.GroupTheory.FreeGroup
open FreeGroup
set_option autoImplicit false

/-!
# Item 3, CoverBound: new content sits in a set of size ≤ 2·|A|

`ComposeBound` proved, per replacement, that the new seam letters come from
`invRev A` (suffix case) or `A` (prefix case).  This module packages that as
the **covering bound**: after the item-2 pass every new letter of every
system word lies in the *new-letter set*

    newLetterSet A := A ∪ letterInv(A)      (as a Finset of letters)

of cardinal at most `2·|A|` (`newLetterSet_card_le`); each word of the
post-pass state is composed of its old letters together with at most that
many new letters (`replace_suffix_new_letters`, `replace_prefix_new_letters`,
and unchanged words are purely old).  Consequently, for a hypothetical
surviving witness at row position `i ≤ p` — the element `w'_{row i}` and its
two neighbours — every letter that was not already present before the pass
lies in `newLetterSet A`, a set of size `≤ 2·|A|`: the genuinely-new content
contributed across the element and its two neighbours is confined to a set of
size at most `2·|A|`, drawn from the balanced first half and its inverses.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- The new-letter set of the pass: the letters of the balanced first half
`A` together with their letter-inverses (the letters of `invRev A`). -/
def newLetterSet {α : Type*} [DecidableEq α] (A : List (α × Bool)) : Finset (α × Bool) :=
  A.toFinset ∪ (A.map letterInv).toFinset

/-- The new-letter set has size at most `2·|A|`. -/
theorem newLetterSet_card_le {α : Type*} [DecidableEq α] (A : List (α × Bool)) :
    (newLetterSet A).card ≤ 2 * A.length := by
  unfold newLetterSet
  have h1 : A.toFinset.card ≤ A.length := List.toFinset_card_le A
  have h2 : (A.map letterInv).toFinset.card ≤ A.length := by
    exact le_trans (List.toFinset_card_le (A.map letterInv)) (by simp)
  have hU := Finset.card_union_le A.toFinset (A.map letterInv).toFinset
  omega

/-- Letters of `invRev A` are letter-inverses of letters of `A` (hence in the
new-letter set). -/
theorem invRev_mem_letterInv {α : Type*} [DecidableEq α] (A : List (α × Bool)) {l : α × Bool}
    (hl : l ∈ FreeGroup.invRev A) : l ∈ (A.map letterInv).toFinset := by
  have hlrev : l ∈ (A.map letterInv).reverse := by
    simpa [FreeGroup.invRev, letterInv] using hl
  have hlr : l ∈ A.map letterInv := by
    simpa [List.mem_reverse] using hlrev
  simpa using hlr

/-- Every letter of the suffix-replacement is old or in the new-letter set. -/
theorem replace_suffix_new_letters {α : Type*} [DecidableEq α]
    (Y A : List (α × Bool)) :
    ∀ l ∈ FreeGroup.reduce (Y ++ FreeGroup.invRev A), l ∈ Y ∨ l ∈ newLetterSet A := by
  intro l hl
  have hmem := reduce_mem (L := Y ++ FreeGroup.invRev A) hl
  rcases List.mem_append.mp hmem with hY | hIA
  · left
    exact hY
  · right
    have hin := invRev_mem_letterInv A hIA
    unfold newLetterSet
    exact Finset.mem_union.mpr (Or.inr hin)

/-- Every letter of the prefix-replacement is old or in the new-letter set. -/
theorem replace_prefix_new_letters {α : Type*} [DecidableEq α]
    (A Y : List (α × Bool)) :
    ∀ l ∈ FreeGroup.reduce (A ++ Y), l ∈ Y ∨ l ∈ newLetterSet A := by
  intro l hl
  have hmem := reduce_mem (L := A ++ Y) hl
  rcases List.mem_append.mp hmem with hA | hY
  · right
    unfold newLetterSet
    have hA' : l ∈ A.toFinset := by simpa using hA
    exact Finset.mem_union.mpr (Or.inl hA')
  · left
    exact hY

end Submission.Nielsen

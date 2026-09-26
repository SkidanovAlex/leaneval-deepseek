import Submission.Work.Item3.RowInvariant

open Submission.Nielsen
open FreeGroup
set_option autoImplicit false

/-!
# The boundary subcase of the ACTIVE TARGET (post-state `i < p` obstruction)

The active target of the Fall-II run route (`Status.lean`) is the post-state
`i < p` word theorem (`RowStrictPostRun`, `Item3/RowInvariant.lean:819`), whose
first concrete half is the `beginAp` obstruction (`RowInvariant.lean:1341`):
in a genuine run to a residual post-state, no row-`< p` even word of the
form `A ++ X` has its second half `X` equal to a *re-creatable* suffix of
`invRev A` (only then could an ends-moved word end with `X`); the `endInv`
mirror is the first-half-`Y`-not-a-prefix-of-`A` claim.  The pure
*reducedness* content at the boundary `|q| = 2|A|` (where the suffix/prefix
has full length, so the word would be `A ++ invRev A`, which fully cancels)
is assembled here into the exact target shape:

* `beginAp_boundary_obstruction` — `IsReduced (A ++ X)`, `|A| = |X|`,
  `A ≠ []` ⟹ `X` is not a suffix of `invRev A`
  (from `RowInvariant.reduced_not_invRev_second_half`, packaged through
  `EndsWithWord` + equal-length-suffix-is-equal);
* `endInv_boundary_obstruction` — `IsReduced (Y ++ invRev A)`, `|Y| = |A|`,
  `A ≠ []` ⟹ `Y` is not a prefix of `A` (the missing mirror; same
  reducedness argument).

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- A suffix of the same length as its word is the whole word. -/
lemma suffix_eq_of_length {α : Type*} (W S : List (α × Bool))
    (hE : EndsWithWord W S) (hlen : W.length = S.length) : W = S := by
  rcases hE with ⟨Y, hW⟩
  have hY : Y = [] := by
    have hlen' : (Y ++ S).length = S.length := by simpa [hW] using hlen
    have hY0 : Y.length = 0 := by
      rw [List.length_append] at hlen'
      omega
    exact List.eq_nil_iff_length_eq_zero.mpr hY0
  calc
    W = Y ++ S := hW
    _ = [] ++ S := by rw [hY]
    _ = S := by simp

/-- A prefix of the same length as its word is the whole word. -/
lemma prefix_eq_of_length {α : Type*} (W S : List (α × Bool))
    (hB : BeginsWithWord W S) (hlen : W.length = S.length) : W = S := by
  rcases hB with ⟨Y, hW⟩
  have hY : Y = [] := by
    have hlen' : (S ++ Y).length = S.length := by simpa [hW] using hlen
    have hY0 : Y.length = 0 := by
      rw [List.length_append] at hlen'
      omega
    exact List.eq_nil_iff_length_eq_zero.mpr hY0
  calc
    W = S ++ Y := hW
    _ = S ++ [] := by rw [hY]
    _ = S := by simp

/-- **The `beginAp` boundary obstruction (ACTIVE-TARGET first half).**  A
reduced word `A ++ X` with `|A| = |X|` never has its second half `X` equal to
a suffix of `invRev A`: any such suffix of length `|X| = |A| = |invRev A|` is
the whole `invRev A`, and `X = invRev A` would make `A ++ X = A ++ invRev A`
non-reduced (`RowInvariant.reduced_not_invRev_second_half`). -/
theorem beginAp_boundary_obstruction {α : Type*} [DecidableEq α]
    (A X : List (α × Bool)) (hA : A ≠ []) (hred : FreeGroup.IsReduced (A ++ X))
    (hlen : A.length = X.length) :
    ¬ EndsWithWord (FreeGroup.invRev A) X := by
  intro hE
  have hlenX : (FreeGroup.invRev A).length = X.length := by
    rw [FreeGroup.invRev_length]
    exact hlen
  have hEq : FreeGroup.invRev A = X := suffix_eq_of_length (FreeGroup.invRev A) X hE hlenX
  exact (reduced_not_invRev_second_half A X hA hred hlen) hEq.symm

/-- **The `endInv` boundary obstruction (ACTIVE-TARGET mirror).**  A reduced
word `Y ++ invRev A` with `|Y| = |A|` never has its first half `Y` equal to a
prefix of `A`: `Y = A` would make `Y ++ invRev A = A ++ invRev A`
non-reduced. -/
theorem endInv_boundary_obstruction {α : Type*} [DecidableEq α]
    (A Y : List (α × Bool)) (hA : A ≠ []) (hred : FreeGroup.IsReduced (Y ++ FreeGroup.invRev A))
    (hlen : A.length = Y.length) :
    ¬ BeginsWithWord A Y := by
  intro hB
  have hEq : A = Y := prefix_eq_of_length A Y hB hlen
  have hred' : FreeGroup.IsReduced (A ++ FreeGroup.invRev A) := by
    simpa [hEq] using hred
  exact not_reduced_append_invRev A hA hred'

end Submission.Nielsen

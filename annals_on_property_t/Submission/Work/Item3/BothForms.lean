import Submission.Work.Item3.BeginApInterior
import Submission.Work.Item3.BeginApBoundary

open Submission.Nielsen
open FreeGroup
set_option autoImplicit false

/-!
# No low word is simultaneously `beginAp` and `endInv` (pure reducedness)

The refined machine structure of genuine-run residual posts (fresh n = 4
collection, `/tmp/fg2/collect_post.py` — see `FallTwoRunNotes.md`): a
row-`< p` even word `q` satisfies

    RightCoverClass(second half) nonempty  ==>  q ends with `invRev A`
    LeftCoverClass(first half)  nonempty  ==>  q begins with `A`

and never both.  The **final step of "never both" is a pure word fact**
proved in this module: a *reduced* word `q` of even length at most
`2·|A|` cannot both begin with `A` and end with `invRev A` (for `A ≠ []`).
Boundary (`|q| = 2|A|`): `q = A ++ X` with `|X| = |A|`, and ending with
`invRev A` forces `X = invRev A`, contradicting `reduced_not_invRev_second_half`
(`A ++ invRev A` is never reduced).  Interior (`|q| < 2|A|`): the second
half of `q` is a proper suffix of `invRev A`, contradicting
`beginAp_interior_obstruction` (also pure reducedness).  All lemmas
kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- Dropping past a whole prefix leaves the rest: `(Y ++ W).drop |Y| = W`. -/
private lemma drop_append_self {α : Type*} (Y W : List (α × Bool)) :
    (Y ++ W).drop Y.length = W := by
  induction Y with
  | nil => simp
  | cons _ Y ih =>
      simpa using ih

/-- **Boundary subcase (`|q| = 2·|A|`).**  A reduced word of length exactly
`2·|A|` that begins with `A` does not end with `invRev A`: the length-`|A|`
suffix of `q` is simultaneously the second half `X` (from `q = A ++ X`) and
the whole `invRev A` (from `q = S ++ invRev A` with `|S| = |A|`),
contradicting `reduced_not_invRev_second_half`. -/
private theorem boundary_no_both_forms {α : Type*} [DecidableEq α]
    (A q : List (α × Bool)) (hA : A ≠ [])
    (hred : FreeGroup.IsReduced q) (hb : q.length = 2 * A.length)
    (hbeg : BeginsWithWord q A) (hend : EndsWithWord q (FreeGroup.invRev A)) :
    False := by
  rcases hbeg with ⟨X, hq⟩
  have hlenX : X.length = A.length := by
    have hlen : (A ++ X).length = 2 * A.length := by simpa [hq] using hb
    rw [List.length_append] at hlen
    omega
  -- the length-|A| suffix of q is X (from q = A ++ X)
  have hXdrop : X = q.drop A.length := by
    rw [hq]
    exact (drop_append_self A X).symm
  -- and it is invRev A (from q = S ++ invRev A, |S| = |A|)
  rcases hend with ⟨S, hqS⟩
  have hSlen : S.length = A.length := by
    have hlen : (S ++ FreeGroup.invRev A).length = 2 * A.length := by
      simpa [hqS] using hb
    rw [List.length_append, FreeGroup.invRev_length] at hlen
    omega
  have hdropS : (S ++ FreeGroup.invRev A).drop A.length = FreeGroup.invRev A := by
    have hd := drop_append_self S (FreeGroup.invRev A)
    simpa [hSlen] using hd
  have hIdrop : FreeGroup.invRev A = q.drop A.length := by
    rw [hqS]
    exact hdropS.symm
  have hEq : FreeGroup.invRev A = X := by
    rw [hIdrop, hXdrop]
  have hred' : FreeGroup.IsReduced (A ++ X) := by simpa [hq] using hred
  exact (reduced_not_invRev_second_half A X hA hred' hlenX.symm) hEq.symm

/-- **Interior subcase (`|q| < 2·|A|`).**  A reduced word of even length
strictly below `2·|A|` that begins with `A` does not end with `invRev A`:
ending with `invRev A` would make the second half of `q` (a proper suffix
of `q`) a suffix of `invRev A`, contradicting `beginAp_interior_obstruction`. -/
private theorem interior_no_both_forms {α : Type*} [DecidableEq α]
    (A q : List (α × Bool)) (hA : A ≠ [])
    (hred : FreeGroup.IsReduced q) (heven : q.length % 2 = 0)
    (hint : q.length < 2 * A.length)
    (hbeg : BeginsWithWord q A) (hend : EndsWithWord q (FreeGroup.invRev A)) :
    False := by
  have hq2 : q.length = 2 * (q.length / 2) := even_length_eq_two_mul q heven
  have hmlt : q.length / 2 < A.length := by
    have : 2 * (q.length / 2) < 2 * A.length := by
      rw [← hq2]
      exact hint
    omega
  have hsuf := suffix_of_EndsWithWord q (FreeGroup.invRev A) (q.length / 2)
    (by rw [FreeGroup.invRev_length]; exact le_of_lt hmlt) hend
  -- hsuf : q.drop (q.length - q.length/2) = (invRev A).drop ((invRev A).length - q.length/2)
  have hlenEq : q.length - q.length / 2 = q.length / 2 := by omega
  rw [hlenEq] at hsuf
  have hsh : EndsWithWord (FreeGroup.invRev A) (secondHalf q) := by
    unfold secondHalf
    refine ⟨(FreeGroup.invRev A).take ((FreeGroup.invRev A).length - q.length / 2), ?_⟩
    rw [hsuf]
    exact (List.take_append_drop ((FreeGroup.invRev A).length - q.length / 2)
      (FreeGroup.invRev A)).symm
  exact beginAp_interior_obstruction A q hA hred hbeg heven hint hsh

/-- **No word is both `beginAp` and `endInv` (pure reducedness).**  A
reduced word `q` of even length at most `2·|A|` cannot both begin with `A`
and end with `invRev A` (for nonempty `A`): at the boundary the suffix
would equal the whole `invRev A` (`A ++ invRev A` never reduced), in the
interior the second half would be a proper suffix of `invRev A`
(`beginAp_interior_obstruction`).  This closes the "never both covering
sides" step of the row-`< p` non-coverability structure of genuine-run
residual posts. -/
theorem no_word_beginAp_endInv {α : Type*} [DecidableEq α]
    (A q : List (α × Bool)) (hA : A ≠ [])
    (hred : FreeGroup.IsReduced q) (heven : q.length % 2 = 0)
    (hle : q.length ≤ 2 * A.length)
    (hbeg : BeginsWithWord q A) (hend : EndsWithWord q (FreeGroup.invRev A)) :
    False := by
  rcases lt_or_eq_of_le hle with hint | hb
  · exact interior_no_both_forms A q hA hred heven hint hbeg hend
  · exact boundary_no_both_forms A q hA hred hb hbeg hend

end Submission.Nielsen

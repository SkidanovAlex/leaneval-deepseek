import Submission.Work.Item3.PassRound
import Submission.Work.Item3.PassDynamics
import Submission.Work.RebalanceProtocol

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
open scoped BigOperators
set_option autoImplicit false

/-!
# Item 3, RoundInvariants: state facts the row-position argument needs

The no-reappearance claim reasons about elements at row positions `i ≤ p` in
the post-pass state and needs to know that their reduced lengths are still at
most `|w_p| = 2·|A|` there.  This module supplies the state-level facts that
make that true, in the no-cancellation regime (any cancellation is a strict
move closing Fall-II):

* `passRound_coord_norm_eq` — after one no-cancellation round at the balanced
  coordinate `c` (halves `A ++ B`, `|A| = |B|`), every coordinate `q ≠ c`
  keeps its reduced length (three-case split on `PassNoCancel` over
  `PassLengths.pass_coord_length_end/_begin`; the balanced coordinate keeps
  its word by `passRound_fix_c`, `passRound_norm_eq_c`);
* `passRound_sorted` — the row order (no element longer than a later one) is
  preserved by the round: lengths are unchanged, so an ordering by length
  stays an ordering by length;
* the two missing orientation facts of the four-case covering table
  (`factor_inv_word_begins_A`, `factor_plus_word_ends_invRevA`): an aggregate
  LEFT neighbour factor `es[j-1] = ± w_v` whose word `X ++ invRev A` covers
  the `A`-half of the balanced element makes the underlying coordinate `w_v`
  begin with `A` (inverse orientation) resp. end with `invRev A` (plus
  orientation) — completing `OldWitness.factor_inv_word_ends` /
  `factor_plus_word_begins` (the right-neighbour cases).  These determine
  which pass classes the neighbour coordinates of any covering witness lie
  in.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/



namespace Submission.Nielsen

/-- **Left covering, inverse orientation.**  If the left neighbour factor is
`es[j-1] = w_v⁻¹` with word `X ++ invRev A` (it covers the `A`-half from the
left), then `w_v`'s word **begins with `A`**. -/
theorem factor_inv_word_begins_A {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) {j : ℕ} (hj : j < es.length) {v : Fin n}
    (A X : List (Fin n × Bool))
    (hleft : (es[j]).toWord = X ++ FreeGroup.invRev A)
    (hv : es[j] = (α (FreeGroup.of v))⁻¹) :
    ∃ Y : List (Fin n × Bool), (α (FreeGroup.of v)).toWord = A ++ Y := by
  refine ⟨FreeGroup.invRev X, ?_⟩
  have hw : (α (FreeGroup.of v)) = (es[j])⁻¹ := by
    rw [hv]
    simp
  calc
    (α (FreeGroup.of v)).toWord = ((es[j])⁻¹).toWord := by rw [hw]
    _ = FreeGroup.invRev (es[j].toWord) := by rw [FreeGroup.toWord_inv]
    _ = FreeGroup.invRev (X ++ FreeGroup.invRev A) := by rw [hleft]
    _ = FreeGroup.invRev (FreeGroup.invRev A) ++ FreeGroup.invRev X := by
        rw [FreeGroup.invRev_append]
    _ = A ++ FreeGroup.invRev X := by rw [FreeGroup.invRev_invRev]

/-- **Left covering, plus orientation.**  If the left neighbour factor is
`es[j-1] = w_v` with word `X ++ invRev A`, then `w_v`'s word ends with
`invRev A`. -/
theorem factor_plus_word_ends_invRevA {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) {j : ℕ} (hj : j < es.length) {v : Fin n}
    (A X : List (Fin n × Bool))
    (hleft : (es[j]).toWord = X ++ FreeGroup.invRev A)
    (hv : es[j] = α (FreeGroup.of v)) :
    ∃ Y : List (Fin n × Bool), (α (FreeGroup.of v)).toWord = Y ++ FreeGroup.invRev A := by
  refine ⟨X, ?_⟩
  rw [← hv]
  exact hleft

/-- Per-coordinate reduced length is preserved by one no-cancellation round. -/
theorem passRound_coord_norm_eq {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (c q : Fin n) (A B : List (Fin n × Bool)) (hqc : q ≠ c)
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B) (hAB : A.length = B.length)
    (hNC : PassNoCancel α c A B (passQ c)) :
    FreeGroup.norm ((α * passRound α c A B) (FreeGroup.of q)) =
      FreeGroup.norm (α (FreeGroup.of q)) := by
  unfold passRound
  rcases hNC q (passQ_mem.mpr hqc) hqc with hE' | hB'
  · rcases hE' with ⟨Y, hqE, h0⟩
    exact pass_coord_length_end α c q A B (passQ c) (passQ_nodup c) (passQ_mem.mpr hqc)
      hqc (passQ_not_mem_c c) hmid hAB Y hqE h0
  · rcases hB' with ⟨hnoE, Y, hqB, h0⟩
    exact pass_coord_length_begin α c q A B (passQ c) (passQ_nodup c) (passQ_mem.mpr hqc)
      hqc (passQ_not_mem_c c) hmid hAB hnoE Y hqB h0

/-- The balanced coordinate keeps its length through a round (its word is
unchanged). -/
theorem passRound_norm_eq_c {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B : List (Fin n × Bool))
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B) :
    FreeGroup.norm ((α * passRound α c A B) (FreeGroup.of c)) =
      FreeGroup.norm (α (FreeGroup.of c)) := by
  change (((α * passRound α c A B) (FreeGroup.of c)).toWord).length =
    ((α (FreeGroup.of c)).toWord).length
  rw [passRound_fix_c α c A B]

/-- **Row sortedness is preserved by a no-cancellation round.**  Since every
coordinate's reduced length is unchanged, an ordering in which no element is
longer than a later one remains such an ordering after the round. -/
theorem passRound_sorted {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (row : Equiv.Perm (Fin n))
    (c : Fin n) (A B : List (Fin n × Bool))
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B) (hAB : A.length = B.length)
    (hNC : PassNoCancel α c A B (passQ c))
    (hsorted : ∀ i j : Fin n, i.val < j.val →
      FreeGroup.norm (α (FreeGroup.of (row i))) ≤ FreeGroup.norm (α (FreeGroup.of (row j)))) :
    ∀ i j : Fin n, i.val < j.val →
      FreeGroup.norm ((α * passRound α c A B) (FreeGroup.of (row i))) ≤
        FreeGroup.norm ((α * passRound α c A B) (FreeGroup.of (row j))) := by
  intro i j hij
  have h1 : FreeGroup.norm ((α * passRound α c A B) (FreeGroup.of (row i))) =
      FreeGroup.norm (α (FreeGroup.of (row i))) := by
    by_cases hc : row i = c
    · subst c
      exact passRound_norm_eq_c α (row i) A B hmid
    · exact passRound_coord_norm_eq α c (row i) A B hc hmid hAB hNC
  have h2 : FreeGroup.norm (α (FreeGroup.of (row j))) =
      FreeGroup.norm ((α * passRound α c A B) (FreeGroup.of (row j))) := by
    by_cases hc : row j = c
    · subst c
      exact (passRound_norm_eq_c α (row j) A B hmid).symm
    · exact (passRound_coord_norm_eq α c (row j) A B hc hmid hAB hNC).symm
  calc
    FreeGroup.norm ((α * passRound α c A B) (FreeGroup.of (row i)))
        = FreeGroup.norm (α (FreeGroup.of (row i))) := h1
    _ ≤ FreeGroup.norm (α (FreeGroup.of (row j))) := hsorted i j hij
    _ = FreeGroup.norm ((α * passRound α c A B) (FreeGroup.of (row j))) := h2

end Submission.Nielsen

import Submission.Work.Item3.OldWitness
import Submission.Work.Item3.SupportBound
import Submission.Work.NielsenPeel

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
open scoped BigOperators
set_option autoImplicit false

/-!
# Item 3, PassLengths: the item-2 pass is length-preserving in the balanced phase

The rebalancing phase of the Fall-II run (`RebalanceProtocol` docs: "the
balanced-phase moves preserve every element's length (`|A_p| = |B_p|`), so the
row stays sorted throughout the run") is built from the item-2 pass
(`item2Pass`: at the balanced coordinate `c` with `w_c = A ++ B`,
`|A| = |B|`, replace the `B`-suffix of every ends-with-`B` element by
`invRev A` and the `B⁻¹`-prefix of every begins-with-`B⁻¹` element by `A`).
This module proves the *length content* of that sentence:

* word level — replacing a `B`-suffix by `invRev A` (`|A| = |B|`) keeps the
  reduced length exactly when there is no boundary cancellation
  (`align Y (invRev A) = 0`): `length_replace_suffix_no_cancel`; the
  `B⁻¹`-prefix mirror `length_replace_prefix_no_cancel`
  (`reduce_no_cancel_of_align_zero` is the underlying fact that a zero
  alignment means the concatenation is already reduced);

* coordinate level — under the item-2 pass over `Q` (`Q` nodup, `c ∉ Q`), an
  affected coordinate `q ∈ Q`, `q ≠ c`:

    pass_coord_length_end   (q ends with `B`, no boundary cancellation) :
        norm ((α·pass)(a_q)) = norm (α(a_q))
    pass_coord_length_begin (q begins with `B⁻¹`, does not end with `B`, no
        boundary cancellation) : norm ((α·pass)(a_q)) = norm (α(a_q))

  (the new word is `reduce (Y ++ invRev A)` resp. `reduce (A ++ Y)` via
  `item2Pass_apply_ends`/`item2Pass_apply_begins` + the word identities of
  `rebalance_join_reduce` / `reduce_middle_empty`; the zero-alignment
  condition makes the replacement exactly length-preserving);

* state level — `pass_N_eq`: if *every* affected coordinate is in the
  no-cancellation regime (`PassNoCancel`), the total length is preserved,
  `N (α·pass) = N α` (the balanced element keeps its word
  `pass_balanced_word_unchanged`, unaffected coordinates are fixed by
  `item2Pass_fix`).

Strictness (`N (α·pass) < N α`) is *not* part of this module: it appears
exactly when a boundary cancellation fires on some combined coordinate, and
those cases are the strict closure moves of `FallII.fallII_*_strict` /
`strict_closure_end_B` / `strict_closure_begin_invB` (single moves, no run
needed).  The run's no-reappearance statement (the genuine remaining
obligation, documented in `NoReappearance.lean`) consumes these
length-preservation facts to know that the row order and the total length do
not move during the balanced phase.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-! ## Word level: zero alignment means the concatenation is reduced -/

/-- `align L M = 0` (both reduced) means no boundary cancellation: the
concatenation `L ++ M` is already reduced. -/
lemma reduce_no_cancel_of_align_zero {α : Type*} [DecidableEq α]
    (L M : List (α × Bool)) (hL : FreeGroup.IsReduced L) (hM : FreeGroup.IsReduced M)
    (h : align L M = 0) : FreeGroup.reduce (L ++ M) = L ++ M := by
  rw [two_word_reduction_shape L M hL hM, h]
  simp

/-- Replacing a `B`-suffix by `invRev A` (`|A| = |B|`) with no boundary
cancellation (`align Y (invRev A) = 0`) keeps the reduced length. -/
lemma length_replace_suffix_no_cancel {α : Type*} [DecidableEq α]
    (Y A B : List (α × Bool)) (hAB : A.length = B.length)
    (hY : FreeGroup.IsReduced Y) (hA : FreeGroup.IsReduced A)
    (h : align Y (FreeGroup.invRev A) = 0) :
    (FreeGroup.reduce (Y ++ FreeGroup.invRev A)).length = (Y ++ B).length := by
  rw [reduce_no_cancel_of_align_zero Y (FreeGroup.invRev A) hY (reduced_invRev A hA) h]
  rw [List.length_append, List.length_append, FreeGroup.invRev_length, hAB]

/-- Replacing a `B⁻¹`-prefix by `A` (`|A| = |B|`) with no boundary
cancellation (`align A Y = 0`) keeps the reduced length. -/
lemma length_replace_prefix_no_cancel {α : Type*} [DecidableEq α]
    (A B Y : List (α × Bool)) (hAB : A.length = B.length)
    (hA : FreeGroup.IsReduced A) (hY : FreeGroup.IsReduced Y)
    (h : align A Y = 0) :
    (FreeGroup.reduce (A ++ Y)).length = (FreeGroup.invRev B ++ Y).length := by
  rw [reduce_no_cancel_of_align_zero A Y hA hY h]
  rw [List.length_append, List.length_append, FreeGroup.invRev_length, hAB]

/-! ## Coordinate level: an affected coordinate keeps its length -/

/-- **Ends-with-`B` coordinate, no boundary cancellation.**  A coordinate
`q ∈ Q` (`q ≠ c`, `c ∉ Q`) whose word is `Y ++ B` (the second half of the
balanced word at `c`), with `align Y (invRev A) = 0` (the new `invRev A`
content does not cancel against the stub `Y`), keeps its reduced length after
the item-2 pass: the `B`-suffix is replaced by the equal-length `invRev A`
with nothing cancelling at the seam. -/
theorem pass_coord_length_end {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (c q : Fin n) (A B : List (Fin n × Bool)) (Q : List (Fin n))
    (hnd : Q.Nodup) (hq : q ∈ Q) (hqc : q ≠ c) (hcQ : c ∉ Q)
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B) (hAB : A.length = B.length)
    (Y : List (Fin n × Bool)) (hqE : (α (FreeGroup.of q)).toWord = Y ++ B)
    (h0 : align Y (FreeGroup.invRev A) = 0) :
    FreeGroup.norm ((α * item2Pass α c A B Q) (FreeGroup.of q)) =
      FreeGroup.norm (α (FreeGroup.of q)) := by
  have happ := item2Pass_apply_ends α c A B Q hnd hq hqc hcQ (by exact ⟨Y, hqE⟩)
  have hw : ((α * item2Pass α c A B Q) (FreeGroup.of q)).toWord =
      FreeGroup.reduce (Y ++ FreeGroup.invRev A) := by
    rw [happ]
    rw [FreeGroup.toWord_mul, FreeGroup.toWord_inv]
    rw [hqE, hmid]
    rw [FreeGroup.invRev_append]
    exact rebalance_join_reduce A B Y
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
  have hlen := length_replace_suffix_no_cancel Y A B hAB hY hA h0
  change (((α * item2Pass α c A B Q) (FreeGroup.of q)).toWord).length =
    ((α (FreeGroup.of q)).toWord).length
  rw [hw]
  rw [hlen]
  rw [hqE]

/-- **Begins-with-`B⁻¹` coordinate, no boundary cancellation.**  A coordinate
`q ∈ Q` (`q ≠ c`, `c ∉ Q`) whose word is `invRev B ++ Y`, that does not end
with `B`, with `align A Y = 0` (the new `A` content does not cancel against
the stub `Y`), keeps its reduced length after the item-2 pass: the
`B⁻¹`-prefix is replaced by the equal-length `A` with nothing cancelling at
the seam. -/
theorem pass_coord_length_begin {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (c q : Fin n) (A B : List (Fin n × Bool)) (Q : List (Fin n))
    (hnd : Q.Nodup) (hq : q ∈ Q) (hqc : q ≠ c) (hcQ : c ∉ Q)
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B) (hAB : A.length = B.length)
    (hnoE : ¬ ∃ Y : List (Fin n × Bool), (α (FreeGroup.of q)).toWord = Y ++ B)
    (Y : List (Fin n × Bool)) (hqB : (α (FreeGroup.of q)).toWord = FreeGroup.invRev B ++ Y)
    (h0 : align A Y = 0) :
    FreeGroup.norm ((α * item2Pass α c A B Q) (FreeGroup.of q)) =
      FreeGroup.norm (α (FreeGroup.of q)) := by
  have happ := item2Pass_apply_begins α c A B Q hnd hq hqc hcQ hnoE (by exact ⟨Y, hqB⟩)
  have hw : ((α * item2Pass α c A B Q) (FreeGroup.of q)).toWord =
      FreeGroup.reduce (A ++ Y) := by
    rw [happ]
    rw [FreeGroup.toWord_mul]
    rw [hmid, hqB]
    rw [show (A ++ B) ++ (FreeGroup.invRev B ++ Y) =
        A ++ ((B ++ FreeGroup.invRev B) ++ Y) by simp [List.append_assoc]]
    rw [reduce_middle_empty (X := A) (M := B ++ FreeGroup.invRev B) (Z := Y)
      (reduce_append_invRev_self B)]
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
  have hlen := length_replace_prefix_no_cancel A B Y hAB hA hY h0
  change (((α * item2Pass α c A B Q) (FreeGroup.of q)).toWord).length =
    ((α (FreeGroup.of q)).toWord).length
  rw [hw]
  rw [hlen]
  rw [hqB]

/-! ## State level: the pass preserves the total length -/

/-- **No-cancellation pass regime.**  Every coordinate `q ∈ Q` (`q ≠ c`)
either ends with `B` and has no boundary cancellation against the new content
(`align Y (invRev A) = 0`), or begins with `B⁻¹`, does not end with `B`, and
has no boundary cancellation against the new content (`align A Y = 0`).  In
this regime every pass move is exactly length-preserving. -/
def PassNoCancel {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B : List (Fin n × Bool)) (Q : List (Fin n)) : Prop :=
  ∀ q : Fin n, q ∈ Q → q ≠ c →
    (∃ Y : List (Fin n × Bool),
      (α (FreeGroup.of q)).toWord = Y ++ B ∧ align Y (FreeGroup.invRev A) = 0) ∨
    (¬ ∃ Y : List (Fin n × Bool), (α (FreeGroup.of q)).toWord = Y ++ B) ∧
      (∃ Y : List (Fin n × Bool),
        (α (FreeGroup.of q)).toWord = FreeGroup.invRev B ++ Y ∧ align A Y = 0)

/-- **The item-2 pass preserves the total length in the no-cancellation
regime.**  At the balanced coordinate `c` (`w_c = A ++ B`, `|A| = |B|`), over
a nodup coordinate set `Q` with `c ∉ Q`, if every affected coordinate is in
the no-cancellation regime (`PassNoCancel`), then `N (α · pass) = N α`: the
balanced element keeps its word (`pass_balanced_word_unchanged`),
unaffected coordinates are fixed (`item2Pass_fix`), and each affected
coordinate keeps its length (`pass_coord_length_end` / `_begin`).  This is
the "Erzeugendenzahl nicht ändert" / row-stays-sorted content of the balanced
phase of the Fall-II run. -/
theorem pass_N_eq {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (c : Fin n) (A B : List (Fin n × Bool)) (Q : List (Fin n))
    (hnd : Q.Nodup) (hcQ : c ∉ Q)
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B) (hAB : A.length = B.length)
    (hNC : PassNoCancel α c A B Q) :
    N (α * item2Pass α c A B Q) = N α := by
  have hnorm : ∀ k : Fin n,
      FreeGroup.norm ((α * item2Pass α c A B Q) (FreeGroup.of k)) =
        FreeGroup.norm (α (FreeGroup.of k)) := by
    intro k
    by_cases hkc : k = c
    · subst k
      have hfix := pass_balanced_word_unchanged α c A B Q hcQ hmid
      change (((α * item2Pass α c A B Q) (FreeGroup.of c)).toWord).length =
        ((α (FreeGroup.of c)).toWord).length
      rw [hfix, hmid]
    · by_cases hkQ : k ∈ Q
      · rcases hNC k hkQ hkc with hE | hB
        · rcases hE with ⟨Y, hY, h0⟩
          exact pass_coord_length_end α c k A B Q hnd hkQ hkc hcQ hmid hAB Y hY h0
        · rcases hB with ⟨hnoE, hBeg⟩
          rcases hBeg with ⟨Y, hY, h0⟩
          exact pass_coord_length_begin α c k A B Q hnd hkQ hkc hcQ hmid hAB hnoE Y hY h0
      · have hfix := item2Pass_fix α c A B Q hkQ
        rw [hfix]
  unfold N
  apply Finset.sum_congr rfl
  intro k hk
  exact hnorm k

end Submission.Nielsen

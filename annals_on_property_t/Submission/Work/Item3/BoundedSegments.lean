import Submission.Work.Item3.RoundInvariants

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
open scoped BigOperators
set_option autoImplicit false

/-!
# Item 3, BoundedSegments: the length and segment premises for row positions <= p

The `SupportBound` analysis of a hypothetical surviving witness at a row
position `i <= p` needs two premises that `RoundInvariants` makes true and
this module packages:

* **post-round lengths are still bounded by `2|A|`**: after a no-cancellation
  round at the balanced coordinate `c` (at row position `p`, word `A ++ B`,
  `|A| = |B|`), every element at a row position `i <= p` has reduced length at
  most `2|A|` — per-coordinate lengths are unchanged
  (`passRound_coord_norm_eq` / `passRound_norm_eq_c`) and the row is sorted
  (`post_round_len_le`, using the hypothesis `hsorted`), so the bound is
  inherited from `w_c = A ++ B`;
* **halves of an absorbed element there are bounded by `|A|`**: an
  exactly-half-absorbed element has even length, so its halves have length at
  most `|A|` (`post_round_half_le`).

Plus the word-level segment reconstruction of the covering halves (the
"Anfangs- und Endbestandteile bis zur Erzeugendenzahl von `A_p`" content):
the left covering half `A'` is the inverse-reversal of the bounded terminal
segment `invRev A'` of the left neighbour word (`cover_half_from_left`), the
right covering half `B'` that of the bounded initial segment `invRev B'`
(`cover_half_from_right`).

These are the premises the no-reappearance contradiction consumes; the
contradiction itself (a genuinely global statement about the post-round
aggregates) remains the open core documented in `FallTwoRunNotes.md`.  Tree
green; only intended sorries `aut_nielsen` (Nielsen.lean:274) and
`theorem_1` (Submission.lean:13).

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/



namespace Submission.Nielsen

/-- Word-level: the covering half is reconstructed from the bounded terminal
segment of the left neighbour's word: the last `|A'|` letters of
`X ++ invRev A'` are `invRev A'`, whose inverse-reversal is `A'`. -/
lemma cover_half_from_left {α : Type*} [DecidableEq α]
    (X A' : List (α × Bool)) :
    FreeGroup.invRev ((X ++ FreeGroup.invRev A').drop X.length) = A' := by
  have hd : (X ++ FreeGroup.invRev A').drop X.length = FreeGroup.invRev A' := by
    simp
  rw [hd]
  rw [FreeGroup.invRev_invRev]

/-- Word-level mirror: the covering half is the inverse-reversal of the
bounded initial segment `invRev B'` of the right neighbour's word. -/
lemma cover_half_from_right {α : Type*} [DecidableEq α]
    (B' Z : List (α × Bool)) :
    FreeGroup.invRev ((FreeGroup.invRev B' ++ Z).take B'.length) = B' := by
  have ht : (FreeGroup.invRev B' ++ Z).take B'.length = FreeGroup.invRev B' := by
    have hb : B'.length = (FreeGroup.invRev B').length := by simp [FreeGroup.invRev_length]
    rw [hb]
    simp
  rw [ht]
  rw [FreeGroup.invRev_invRev]

/-- **Post-round length bound at row positions ≤ p.**  After a no-cancellation
round at the balanced coordinate `c` (`c` at row position `p`, word
`A ++ B`, `|A| = |B|`), every element at a row position `i ≤ p` has reduced
length at most `2·|A|`: per-coordinate lengths are unchanged by the round
(`passRound_coord_norm_eq` / `passRound_norm_eq_c`) and the row is sorted
(the hypothesis `hsorted`), so the bound is inherited from `w_c = A ++ B`. -/
theorem post_round_len_le {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B : List (Fin n × Bool)) (row : Equiv.Perm (Fin n)) (p : Fin n)
    (hrowp : row p = c)
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B) (hAB : A.length = B.length)
    (hNC : PassNoCancel α c A B (passQ c))
    (hsorted : ∀ i j : Fin n, i.val < j.val →
      FreeGroup.norm (α (FreeGroup.of (row i))) ≤ FreeGroup.norm (α (FreeGroup.of (row j)))) :
    ∀ i : Fin n, i.val ≤ p.val →
      FreeGroup.norm ((α * passRound α c A B) (FreeGroup.of (row i))) ≤ 2 * A.length := by
  intro i hip
  have hlen_eq : FreeGroup.norm ((α * passRound α c A B) (FreeGroup.of (row i))) =
      FreeGroup.norm (α (FreeGroup.of (row i))) := by
    by_cases hc : row i = c
    · rw [hc]
      exact passRound_norm_eq_c α c A B hmid
    · exact passRound_coord_norm_eq α c (row i) A B hc hmid hAB hNC
  rw [hlen_eq]
  have hwi : FreeGroup.norm (α (FreeGroup.of (row i))) ≤
      FreeGroup.norm (α (FreeGroup.of (row p))) := by
    rcases lt_or_eq_of_le hip with hip_lt | hip_eq
    · exact hsorted i p hip_lt
    · have hIp : row i = row p := by
        exact congrArg row (Fin.ext hip_eq)
      rw [hIp]
  have hwc : FreeGroup.norm (α (FreeGroup.of (row p))) = 2 * A.length := by
    rw [hrowp]
    change ((α (FreeGroup.of c)).toWord).length = 2 * A.length
    rw [hmid]
    rw [List.length_append]
    omega
  rw [hwc] at hwi
  exact hwi

/-- **Halves of an absorbed element at a row position ≤ p are bounded by
`|A|`.**  If the post-round element at row position `i ≤ p` has even reduced
length `2·k'` (as an exactly-half-absorbed element would), then
`k' ≤ |A|`. -/
theorem post_round_half_le {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B : List (Fin n × Bool)) (row : Equiv.Perm (Fin n)) (p : Fin n)
    (hrowp : row p = c)
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B) (hAB : A.length = B.length)
    (hNC : PassNoCancel α c A B (passQ c))
    (hsorted : ∀ i j : Fin n, i.val < j.val →
      FreeGroup.norm (α (FreeGroup.of (row i))) ≤ FreeGroup.norm (α (FreeGroup.of (row j)))) :
    ∀ i : Fin n, i.val ≤ p.val → ∀ k' : ℕ,
      FreeGroup.norm ((α * passRound α c A B) (FreeGroup.of (row i))) = 2 * k' →
        k' ≤ A.length := by
  intro i hip k' hk
  have hle := post_round_len_le α c A B row p hrowp hmid hAB hNC hsorted i hip
  rw [hk] at hle
  omega

end Submission.Nielsen

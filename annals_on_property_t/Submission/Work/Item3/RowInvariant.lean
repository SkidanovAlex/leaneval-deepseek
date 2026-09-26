import Submission.Work.Item3.PostRoundSupport
import Submission.Work.Item3.BoundedSegments
import Submission.Work.Item3.FixpointFirst
import Submission.Work.RebalanceProtocol
import Submission.Work.NielsenResidual
import Submission.Commons.GroupTheory.FreeGroup.reduce_append_invRev_right
import Mathlib.Tactic.Group

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
open scoped BigOperators
set_option autoImplicit false

/-!
# Item 3, RowInvariant: the row-`< p` invariant of the fixpoint pass

The `i < p` no-reappearance case (machine-validated at volume: after the
fixpoint pass at the balanced coordinate `c` — row position `p`, own halves
`A_p B_p` — no coordinate at a row position `< p` with an even-length word is
two-sidedly coverable; 0 of 1000 at n = 3) is the **row-`< p` invariant**.
No local hypothesis weaker than the full configuration suffices (length
bound, global shortness, per-word privacy of halves, plus-RIGHT emptiness
were all machine-refuted; see `FallTwoRunNotes.md`), so the invariant's
three hypotheses — **row ordering (sortedness), bounded lengths, fixpoint
closure (`NoPassActive`)** — must act together.

This module supplies the *length premise at the fixpoint*: the pass is
`passIter K` (several rounds), and the bounded-length fact must hold after
all `K` rounds, not just one.  The one-round versions
(`RoundInvariants.passRound_sorted`, `BoundedSegments.post_round_len_le`)
are extended to any number of no-cancellation rounds:

    passIter_rec            : (α·γ)·passIter t (α·γ) = α·passIter (t+1) α
                              (γ = passRound α)     -- the recursion identity
    passIter_coord_norm_eq  : every coordinate keeps its reduced length
                              through K no-cancellation rounds
    passIter_sorted         : the row order survives K rounds
    passIter_len_le         : rows i <= p keep length <= 2|A| after K rounds

(The per-round hypothesis `hNC : forall t < K, PassNoCancel (α·passIter t α)
c A B (passQ c)` is the fixpoint closure restricted to the no-cancellation
regime: any cancelled round is a strict move closing Fall-II immediately.)

**Open target (the invariant itself, unproven):** with the three hypotheses
acting together, every coordinate at a row position `< p` with even word
length is not two-sidedly coverable — the word theorem of the `i < p` case;
its proof mechanism is still unidentified (no fabricated lemma is committed).

**Two-sided coverability is one condition (proved below).**  The two
"orientations" in `TwoSidedCoverable` (halves `(A',B')` of `W`, or the halves
`(invRev B', invRev A')` of `W^-1`) coincide: the right-covering class of
`invRev A'` is the left-covering class of `A'` (`RightCoverClass_invRev_eq_LeftCoverClass`)
and the left-covering class of `invRev B'` is the right-covering class of
`B'` (`LeftCoverClass_invRev_eq_RightCoverClass`); hence
`orientationCovered_orientation_iff`, `twoSidedCoverable_iff_orientation` and
`twoSidedCoverable_iff_single` (`TwoSidedCoverable ⟷ RC (secondHalf) ∧ LC (firstHalf)`).
So the open invariant reads: for an even word at a row position `< p`, at
least one of the two classes — the left-covering class of the first half or
the right-covering class of the second half — is empty.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/



namespace Submission.Nielsen

/-- The pass recursion identity: one round followed by `t` more rounds (each
computed against the evolving automorphism) is the state after `t + 1`
rounds. -/
lemma passIter_rec {n : ℕ} (t : ℕ) (α : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B : List (Fin n × Bool)) :
    (α * passRound α c A B) * passIter t (α * passRound α c A B) c A B =
      α * passIter (t + 1) α c A B := by
  rw [passIter]
  rw [mul_assoc]

/-- Per-coordinate norms are preserved through any number of no-cancellation
rounds (each round needs its own `PassNoCancel` at the intermediate
automorphism). -/
theorem passIter_coord_norm_eq {n : ℕ} (K : ℕ) (α : MulAut (FreeGroup (Fin n)))
    (c q : Fin n) (A B : List (Fin n × Bool))
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B) (hAB : A.length = B.length)
    (hNC : ∀ t : ℕ, t < K → PassNoCancel (α * passIter t α c A B) c A B (passQ c)) :
    FreeGroup.norm ((α * passIter K α c A B) (FreeGroup.of q)) =
      FreeGroup.norm (α (FreeGroup.of q)) := by
  revert hmid hAB hNC
  induction K generalizing α with
  | zero =>
      intro hmid hAB hNC
      simp [passIter]
  | succ K ih =>
      intro hmid hAB hNC
      let γ : MulAut (FreeGroup (Fin n)) := passRound α c A B
      have hrec : (α * γ) * passIter K (α * γ) c A B = α * passIter (K + 1) α c A B := by
        simpa [γ] using (passIter_rec K α c A B)
      have hmid1 : ((α * γ) (FreeGroup.of c)).toWord = A ++ B := by
        change ((α * passRound α c A B) (FreeGroup.of c)).toWord = A ++ B
        rw [passRound_fix_c α c A B]
        exact hmid
      have hNC' : ∀ t : ℕ, t < K →
          PassNoCancel ((α * γ) * passIter t (α * γ) c A B) c A B (passQ c) := by
        intro t ht
        have ht' : t + 1 < K + 1 := by omega
        have h := hNC (t + 1) ht'
        rwa [← passIter_rec t α c A B] at h
      have hround : FreeGroup.norm ((α * γ) (FreeGroup.of q)) =
          FreeGroup.norm (α (FreeGroup.of q)) := by
        by_cases hqc : q = c
        · subst q
          exact passRound_norm_eq_c α c A B hmid
        · exact passRound_coord_norm_eq α c q A B hqc hmid hAB (hNC 0 (by omega))
      have hrest : FreeGroup.norm (((α * γ) * passIter K (α * γ) c A B) (FreeGroup.of q)) =
          FreeGroup.norm ((α * γ) (FreeGroup.of q)) :=
        ih (α := α * γ) hmid1 hAB hNC'
      calc
        FreeGroup.norm ((α * passIter (K + 1) α c A B) (FreeGroup.of q))
            = FreeGroup.norm (((α * γ) * passIter K (α * γ) c A B) (FreeGroup.of q)) := by
                rw [← hrec]
        _ = FreeGroup.norm ((α * γ) (FreeGroup.of q)) := hrest
        _ = FreeGroup.norm (α (FreeGroup.of q)) := hround

/-- Row sortedness is preserved through any number of no-cancellation rounds
(per-coordinate norms are unchanged, `passIter_coord_norm_eq`). -/
theorem passIter_sorted {n : ℕ} (K : ℕ) (α : MulAut (FreeGroup (Fin n)))
    (c : Fin n) (A B : List (Fin n × Bool)) (row : Equiv.Perm (Fin n))
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B) (hAB : A.length = B.length)
    (hNC : ∀ t : ℕ, t < K → PassNoCancel (α * passIter t α c A B) c A B (passQ c))
    (hsorted : ∀ i j : Fin n, i.val < j.val →
      FreeGroup.norm (α (FreeGroup.of (row i))) ≤ FreeGroup.norm (α (FreeGroup.of (row j)))) :
    ∀ i j : Fin n, i.val < j.val →
      FreeGroup.norm ((α * passIter K α c A B) (FreeGroup.of (row i))) ≤
        FreeGroup.norm ((α * passIter K α c A B) (FreeGroup.of (row j))) := by
  intro i j hij
  have h1 : FreeGroup.norm ((α * passIter K α c A B) (FreeGroup.of (row i))) =
      FreeGroup.norm (α (FreeGroup.of (row i))) :=
    passIter_coord_norm_eq K α c (row i) A B hmid hAB hNC
  have h2 : FreeGroup.norm ((α * passIter K α c A B) (FreeGroup.of (row j))) =
      FreeGroup.norm (α (FreeGroup.of (row j))) :=
    passIter_coord_norm_eq K α c (row j) A B hmid hAB hNC
  calc
    FreeGroup.norm ((α * passIter K α c A B) (FreeGroup.of (row i)))
        = FreeGroup.norm (α (FreeGroup.of (row i))) := h1
    _ ≤ FreeGroup.norm (α (FreeGroup.of (row j))) := hsorted i j hij
    _ = FreeGroup.norm ((α * passIter K α c A B) (FreeGroup.of (row j))) := h2.symm

/-- **Length premise at the fixpoint (`K` rounds).**  After any number of
no-cancellation rounds at the balanced coordinate `c` (at row position `p`,
word `A ++ B`, `|A| = |B|`), every element at a row position `i <= p` has
reduced length at most `2|A|`: per-coordinate norms are unchanged through the
rounds (`passIter_coord_norm_eq`) and the row stays sorted
(`passIter_sorted`), so the bound is inherited from `w_c = A ++ B`.  This is
the multi-round (fixpoint) version of `BoundedSegments.post_round_len_le`,
and the first verified premise of the row-`< p` invariant. -/
theorem passIter_len_le {n : ℕ} (K : ℕ) (α : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B : List (Fin n × Bool)) (row : Equiv.Perm (Fin n)) (p : Fin n)
    (hrowp : row p = c)
    (hmid : (α (FreeGroup.of c)).toWord = A ++ B) (hAB : A.length = B.length)
    (hNC : ∀ t : ℕ, t < K → PassNoCancel (α * passIter t α c A B) c A B (passQ c))
    (hsorted : ∀ i j : Fin n, i.val < j.val →
      FreeGroup.norm (α (FreeGroup.of (row i))) ≤ FreeGroup.norm (α (FreeGroup.of (row j)))) :
    ∀ i : Fin n, i.val ≤ p.val →
      FreeGroup.norm ((α * passIter K α c A B) (FreeGroup.of (row i))) ≤ 2 * A.length := by
  intro i hip
  have h1 : FreeGroup.norm ((α * passIter K α c A B) (FreeGroup.of (row i))) =
      FreeGroup.norm (α (FreeGroup.of (row i))) :=
    passIter_coord_norm_eq K α c (row i) A B hmid hAB hNC
  rw [h1]
  have hwi : FreeGroup.norm (α (FreeGroup.of (row i))) ≤
      FreeGroup.norm (α (FreeGroup.of (row p))) := by
    rcases lt_or_eq_of_le hip with hip_lt | hip_eq
    · exact hsorted i p hip_lt
    · have hIp : row i = row p := by exact congrArg row (Fin.ext hip_eq)
      rw [hIp]
  have hwc : FreeGroup.norm (α (FreeGroup.of (row p))) = 2 * A.length := by
    rw [hrowp]
    change ((α (FreeGroup.of c)).toWord).length = 2 * A.length
    rw [hmid]
    rw [List.length_append]
    omega
  rw [hwc] at hwi
  exact hwi

/-! ## Two-sided coverability (the word-level vocabulary of the invariant) -/

/-- `L` is a suffix of `W` (as lists of letters). -/
def EndsWithWord {α : Type*} (W L : List (α × Bool)) : Prop :=
  ∃ Y : List (α × Bool), W = Y ++ L

/-- `L` is a prefix of `W`. -/
def BeginsWithWord {α : Type*} (W L : List (α × Bool)) : Prop :=
  ∃ Y : List (α × Bool), W = L ++ Y

/-- The word of a coordinate. -/
def coordWord {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (q : Fin n) : List (Fin n × Bool) :=
  (α (FreeGroup.of q)).toWord

/-- **Right-covering class.**  A coordinate `u != q` whose word ends with the
half `B'` (so its inverse factor `w_u⁻¹` covers `invRev B'` from the right in
the minus orientation) or begins with `invRev B'` (the plus orientation):
exactly the word classes an aggregate right neighbour of a half-absorbed
the factor `= w_q` or `= w_q^(-1)` must lie in (`OldWitness`, `RoundInvariants` orientation table). -/
def RightCoverClass {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (q : Fin n)
    (B' : List (Fin n × Bool)) : Prop :=
  ∃ u : Fin n, u ≠ q ∧
    (EndsWithWord (coordWord α u) B' ∨ BeginsWithWord (coordWord α u) (FreeGroup.invRev B'))

/-- **Left-covering class.**  A coordinate `v != q` whose word ends with
`invRev A'` (plus orientation) or begins with `A'` (minus orientation). -/
def LeftCoverClass {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (q : Fin n)
    (A' : List (Fin n × Bool)) : Prop :=
  ∃ v : Fin n, v ≠ q ∧
    (EndsWithWord (coordWord α v) (FreeGroup.invRev A') ∨ BeginsWithWord (coordWord α v) A')

/-- One **orientation** of an even word with halves `A' B'` is covered when
both covering classes are inhabited. -/
def OrientationCovered {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (q : Fin n)
    (A' B' : List (Fin n × Bool)) : Prop :=
  RightCoverClass α q B' ∧ LeftCoverClass α q A'

/-- The first and second halves of a word of even length. -/
def firstHalf {α : Type*} (W : List (α × Bool)) : List (α × Bool) := W.take (W.length / 2)
def secondHalf {α : Type*} (W : List (α × Bool)) : List (α × Bool) := W.drop (W.length / 2)

/-- **Two-sidedly coverable.**  The word of coordinate `q` has even length
and admits a two-sided covering in at least one orientation: with halves
`A' B'` (the factor `= w_q`) or with the halves of the inverse word
`(invRev B', invRev A')` (the factor `= w_q⁻¹`), both the right and the left
covering class are inhabited by coordinates other than `q`.  This is the
word-level necessary condition for `q` to be the balanced element of a
confined half-absorption witness (`ExactlyHalfAbsorbed`).  The row-`< p`
invariant asserts its negation for every even-length coordinate at a row
position `< p` after the fixpoint. -/
def TwoSidedCoverable {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (q : Fin n) : Prop :=
  let W := coordWord α q
  let A' := firstHalf W
  let B' := secondHalf W
  (OrientationCovered α q A' B' ∨ OrientationCovered α q (FreeGroup.invRev B') (FreeGroup.invRev A'))

/-! ## Forced facts about halves and covering classes (provable infrastructure)

These are the provable consequences of the vocabulary that any proof of the
row-`< p` invariant must use.  **Deliberately absent** (per the two-sorry
rule and the machine record in `FallTwoRunNotes.md`): a `sorry`-stated
"first forced contradiction".  Machine data shows that under ALL THREE
hypotheses (sortedness, bounded length `<= 2|A|`, `NoPassActive`) coverable
elements of length `<= 2|A|` exist at rows `> p` — so no single hypothesis
contradicts `TwoSidedCoverable`; only the row-`< p` index does, through a
mechanism not yet identified.  Nothing below overclaims it.
-/

/-- The two halves of an even word reassemble it. -/
lemma firstHalf_append_secondHalf {α : Type*} (W : List (α × Bool)) :
    firstHalf W ++ secondHalf W = W := by
  unfold firstHalf secondHalf
  rw [List.take_append_drop]

/-- The first half has length `|W| / 2`. -/
lemma firstHalf_length {α : Type*} (W : List (α × Bool)) :
    (firstHalf W).length = W.length / 2 := by
  unfold firstHalf
  rw [List.length_take]
  rw [min_eq_left (by omega : W.length / 2 ≤ W.length)]

/-- For an even word `W` (`|W| = 2 * k`) both halves have length `k`. -/
lemma half_length_of_even {α : Type*} (W : List (α × Bool)) (k : ℕ)
    (h : W.length = 2 * k) :
    (firstHalf W).length = k ∧ (secondHalf W).length = k := by
  constructor
  · rw [firstHalf_length, h]
    omega
  · unfold secondHalf
    rw [h]
    have hd : (2 * k) / 2 = k := by omega
    rw [hd]
    rw [List.length_drop]
    omega

/-- `L` is a suffix of `X ++ L`. -/
lemma EndsWithWord_append {α : Type*} (X L : List (α × Bool)) :
    EndsWithWord (X ++ L) L := by
  unfold EndsWithWord
  exact ⟨X, rfl⟩

/-- `L` is a prefix of `L ++ Y`. -/
lemma BeginsWithWord_append {α : Type*} (L Y : List (α × Bool)) :
    BeginsWithWord (L ++ Y) L := by
  unfold BeginsWithWord
  exact ⟨Y, rfl⟩

/-- A suffix has length at most the whole word. -/
lemma EndsWithWord_length_le {α : Type*} {W L : List (α × Bool)}
    (h : EndsWithWord W L) : L.length ≤ W.length := by
  rcases h with ⟨Y, rfl⟩
  simp

/-- A prefix has length at most the whole word. -/
lemma BeginsWithWord_length_le {α : Type*} {W L : List (α × Bool)}
    (h : BeginsWithWord W L) : L.length ≤ W.length := by
  rcases h with ⟨Y, rfl⟩
  simp

/-- The word of coordinate `q` has even length `2k` iff both halves have
length `k` and reassemble it: the exact shape `TwoSidedCoverable` reasons
with. -/
lemma coordWord_even_halves {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (q : Fin n)
    (k : ℕ) (h : (coordWord α q).length = 2 * k) :
    (firstHalf (coordWord α q)).length = k ∧
      (secondHalf (coordWord α q)).length = k ∧
      firstHalf (coordWord α q) ++ secondHalf (coordWord α q) = coordWord α q := by
  exact ⟨(half_length_of_even (coordWord α q) k h).1,
    (half_length_of_even (coordWord α q) k h).2, firstHalf_append_secondHalf (coordWord α q)⟩

/-- A right coverer supplied by an ending word has length at least the half
it covers. -/
lemma RightCoverClass_end_length {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (q : Fin n)
    (B' : List (Fin n × Bool)) (h : RightCoverClass α q B') :
    ∃ u : Fin n, u ≠ q ∧ (coordWord α u).length ≥ B'.length := by
  rcases h with ⟨u, hu, hc⟩
  rcases hc with hEnd | hBeg
  · exact ⟨u, hu, EndsWithWord_length_le hEnd⟩
  · refine ⟨u, hu, ?_⟩
    have hle : B'.length ≤ (FreeGroup.invRev B').length := by
      rw [FreeGroup.invRev_length]
    exact le_trans hle (BeginsWithWord_length_le hBeg)


/-! ## The two orientations of two-sided coverability coincide

`TwoSidedCoverable` is defined as `OrientationCovered ... A' B' ∨
OrientationCovered ... (invRev B') (invRev A')` — the two "orientations" of
an even word `W = A' B'` (the factor `= w_q`, or the factor `= w_q⁻¹`, whose
halves are `(invRev B', invRev A')`).  Unfolding the covering classes shows
that the two orientations are in fact the *same* predicate: the right-covering
class of the swapped half `invRev A'` (`ends with invRev A'` or `begins with
A'`) is exactly the left-covering class of `A'`, and the left-covering class
of `invRev B'` (`ends with B'` or `begins with invRev B'`) is exactly the
right-covering class of `B'`.  So two-sided coverability is the single
conjunction: the *left* covering class of the first half and the *right*
covering class of the second half are both inhabited by coordinates other
than `q`.  This collapses the orientation table: the machine reports of
"which side is empty in which orientation" (`FallTwoRunNotes.md`) describe
one and the same deficiency, and the open row-`< p` invariant is: for an
even word at a row position `< p`, at least one of the two classes
(`LeftCoverClass` of the first half, `RightCoverClass` of the second half)
is empty. -/

/-- The right-covering class of an inverse-reversed half is the left-covering
class of the half itself. -/
lemma RightCoverClass_invRev_eq_LeftCoverClass {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (q : Fin n) (A' : List (Fin n × Bool)) :
    RightCoverClass α q (FreeGroup.invRev A') ↔ LeftCoverClass α q A' := by
  constructor
  · rintro ⟨u, hu, hc⟩
    refine ⟨u, hu, ?_⟩
    rcases hc with hE | hB
    · exact Or.inl hE
    · right
      rcases hB with ⟨Y, hY⟩
      refine ⟨Y, ?_⟩
      rw [FreeGroup.invRev_invRev] at hY
      exact hY
  · rintro ⟨v, hv, hc⟩
    refine ⟨v, hv, ?_⟩
    rcases hc with hE | hB
    · left
      exact hE
    · right
      rcases hB with ⟨Y, hY⟩
      refine ⟨Y, ?_⟩
      rw [FreeGroup.invRev_invRev]
      exact hY

/-- The left-covering class of an inverse-reversed half is the right-covering
class of the half itself. -/
lemma LeftCoverClass_invRev_eq_RightCoverClass {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (q : Fin n) (B' : List (Fin n × Bool)) :
    LeftCoverClass α q (FreeGroup.invRev B') ↔ RightCoverClass α q B' := by
  constructor
  · rintro ⟨v, hv, hc⟩
    refine ⟨v, hv, ?_⟩
    rcases hc with hE | hB
    · left
      rcases hE with ⟨Y, hY⟩
      refine ⟨Y, ?_⟩
      rw [FreeGroup.invRev_invRev] at hY
      exact hY
    · exact Or.inr hB
  · rintro ⟨u, hu, hc⟩
    refine ⟨u, hu, ?_⟩
    rcases hc with hE | hB
    · left
      rcases hE with ⟨Y, hY⟩
      refine ⟨Y, ?_⟩
      rw [FreeGroup.invRev_invRev]
      exact hY
    · exact Or.inr hB

/-- The two orientations of an even word define the same covering predicate:
`OrientationCovered` with the halves `(A', B')` and with the halves of the
inverse word `(invRev B', invRev A')` coincide. -/
theorem orientationCovered_orientation_iff {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (q : Fin n) (A' B' : List (Fin n × Bool)) :
    OrientationCovered α q A' B' ↔
      OrientationCovered α q (FreeGroup.invRev B') (FreeGroup.invRev A') := by
  unfold OrientationCovered
  rw [RightCoverClass_invRev_eq_LeftCoverClass (α := α) (q := q) (A' := A'),
      LeftCoverClass_invRev_eq_RightCoverClass (α := α) (q := q) (B' := B')]
  exact and_comm

/-- **Two-sided coverability is one condition.**  Both orientations of the
covering test are the same predicate (`orientationCovered_orientation_iff`),
so `TwoSidedCoverable α q` is equivalent to either orientation — the single
conjunction "the left covering class of the first half and the right covering
class of the second half are both inhabited by coordinates other than `q`". -/
theorem twoSidedCoverable_iff_orientation {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (q : Fin n) :
    TwoSidedCoverable α q ↔
      OrientationCovered α q (firstHalf (coordWord α q)) (secondHalf (coordWord α q)) := by
  dsimp [TwoSidedCoverable]
  constructor
  · rintro (hP | hM)
    · exact hP
    · exact (orientationCovered_orientation_iff α q
        (firstHalf (coordWord α q)) (secondHalf (coordWord α q))).mpr hM
  · exact Or.inl


/-- **The single-condition form.**  `TwoSidedCoverable α q` is the
conjunction of the two covering classes of the two halves of `q`'s word: the
*left* covering class of the first half (`LeftCoverClass α q A'`) and the
*right* covering class of the second half (`RightCoverClass α q B'`), with
`A' B'` the halves of `coordWord α q`.  Any proof of the row-`< p`
invariant splits on this conjunction. -/
theorem twoSidedCoverable_iff_single {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (q : Fin n) :
    TwoSidedCoverable α q ↔
      RightCoverClass α q (secondHalf (coordWord α q)) ∧
        LeftCoverClass α q (firstHalf (coordWord α q)) := by
  rw [twoSidedCoverable_iff_orientation]
  unfold OrientationCovered
  rfl


/-- The halves of an even split `A ++ B` (`|A| = |B|`) are `A` and `B`. -/
lemma firstHalf_append_eq {α : Type*} (A B : List (α × Bool)) (h : A.length = B.length) :
    firstHalf (A ++ B) = A ∧ secondHalf (A ++ B) = B := by
  constructor
  · unfold firstHalf
    have hlen : (A ++ B).length / 2 = A.length := by
      rw [List.length_append, h]
      omega
    rw [hlen]
    rw [List.take_append_of_le_length (l₁ := A) (l₂ := B) (i := A.length)
      (by rfl : A.length ≤ A.length)]
    simp
  · unfold secondHalf
    have hlen : (A ++ B).length / 2 = A.length := by
      rw [List.length_append, h]
      omega
    rw [hlen]
    rw [List.drop_append_of_le_length (l₁ := A) (l₂ := B) (i := A.length)
      (by rfl : A.length ≤ A.length)]
    simp

/-! ## The `i = p` base case: the balanced coordinate is not coverable at the fixpoint

`NoPassActive α' c A B` says that after the fixpoint pass no coordinate other
than `c` ends with the second half `B` of `c`'s word or begins with its
inverse `B⁻¹`.  But the *right covering class* of `c`'s second half is
exactly that pair of classes — so the right side of `c`'s own two-sided
covering is empty, and by the single-condition form
(`twoSidedCoverable_iff_single`) `c` is not two-sidedly coverable at all.
This is the `i = p` case of the row-`< p` invariant at the word level. -/

/-- Under the fixpoint predicate the right covering class of the second half
`B` is empty. -/
theorem noRightCoverClass_of_NoPassActive {n : ℕ} (α' : MulAut (FreeGroup (Fin n)))
    (c : Fin n) (A B : List (Fin n × Bool)) (hfix : NoPassActive α' c A B) :
    ¬ RightCoverClass α' c B := by
  intro hRC
  rcases hRC with ⟨u, hu, hE | hB⟩
  · rcases hE with ⟨Y, hY⟩
    exact (hfix u hu).1 ⟨Y, by simpa [coordWord] using hY⟩
  · rcases hB with ⟨Y, hY⟩
    exact (hfix u hu).2 ⟨Y, by simpa [coordWord] using hY⟩

/-- **The balanced coordinate is not two-sidedly coverable at the fixpoint
(the `i = p` word-level base).**  If `c`'s word is `A ++ B` with `|A| = |B|`
and the fixpoint predicate holds at `c`, then `c` itself is not
two-sidedly coverable: its right covering class would need a coordinate
`u ≠ c` ending with `B` or beginning with `B⁻¹`, exactly the classes emptied
by the fixpoint. -/
theorem fixpoint_balanced_c_not_coverable {n : ℕ} (α' : MulAut (FreeGroup (Fin n)))
    (c : Fin n) (A B : List (Fin n × Bool)) (hfix : NoPassActive α' c A B)
    (hmid : (α' (FreeGroup.of c)).toWord = A ++ B) (hAB : A.length = B.length) :
    ¬ TwoSidedCoverable α' c := by
  rw [twoSidedCoverable_iff_single]
  have hc : coordWord α' c = A ++ B := by
    unfold coordWord
    exact hmid
  rw [hc]
  rcases firstHalf_append_eq A B hAB with ⟨hA, hB⟩
  rw [hB, hA]
  intro h
  exact noRightCoverClass_of_NoPassActive α' c A B hfix h.1


/-! ## The rows-`< p` invariant reduces the full claim (structural side)

The no-reappearance invariant of the run is "no coordinate at a row position
`<= p` is two-sidedly coverable after the fixpoint pass".  Its `i = p`
half is closed (`fixpoint_balanced_c_not_coverable`: the balanced coordinate
`c` itself is not coverable, because its right covering class is exactly the
pair of classes the fixpoint empties).  So the full claim reduces to its
`i < p` half: an even word at a row position strictly below `p` is not
two-sidedly coverable.  This is the open word theorem of the `i < p` case;
the reduction below is the structural side that lets any proof of the
`i < p` claim close the invariant. -/

/-- The invariant restricted to row positions strictly below `p`. -/
def RowInvariantStrict {n : ℕ} (α' : MulAut (FreeGroup (Fin n)))
    (row : Equiv.Perm (Fin n)) (p : Fin n) : Prop :=
  ∀ q : Fin n, (row.symm q).val < p.val → ¬ TwoSidedCoverable α' q

/-- The invariant at row positions `<= p`. -/
def RowInvariantLe {n : ℕ} (α' : MulAut (FreeGroup (Fin n)))
    (row : Equiv.Perm (Fin n)) (p : Fin n) : Prop :=
  ∀ q : Fin n, (row.symm q).val ≤ p.val → ¬ TwoSidedCoverable α' q

/-- **The `i = p` base closes the invariant at `p` itself.**  If `c` sits at
row position `p` with word `A ++ B` (`|A| = |B|`) and the fixpoint predicate
holds at `c`, then `c` is not two-sidedly coverable — the `q = c` instance of
`RowInvariantLe`. -/
theorem rowInvariantLe_at_p {n : ℕ} (α' : MulAut (FreeGroup (Fin n)))
    (row : Equiv.Perm (Fin n)) (p : Fin n) (c : Fin n) (hrowp : row p = c)
    (A B : List (Fin n × Bool)) (hfix : NoPassActive α' c A B)
    (hmid : (α' (FreeGroup.of c)).toWord = A ++ B) (hAB : A.length = B.length) :
    ¬ TwoSidedCoverable α' c :=
  fixpoint_balanced_c_not_coverable α' c A B hfix hmid hAB

/-- **Reduction of the invariant to its `i < p` half.**  Given the fixpoint
at the balanced coordinate `c` (row position `p`, word `A ++ B`,
`|A| = |B|`), the invariant at row positions `<= p` is equivalent to the
invariant at row positions `< p`: the only additional instance is `q = c`,
which is closed by `fixpoint_balanced_c_not_coverable`.  Hence any proof of
`RowInvariantStrict` (the open `i < p` word theorem) completes the full
no-reappearance claim. -/
theorem rowInvariantLe_iff_strict {n : ℕ} (α' : MulAut (FreeGroup (Fin n)))
    (row : Equiv.Perm (Fin n)) (p : Fin n) (c : Fin n) (hrowp : row p = c)
    (A B : List (Fin n × Bool)) (hfix : NoPassActive α' c A B)
    (hmid : (α' (FreeGroup.of c)).toWord = A ++ B) (hAB : A.length = B.length) :
    RowInvariantLe α' row p ↔ RowInvariantStrict α' row p := by
  constructor
  · intro h q hq
    exact h q (le_of_lt hq)
  · intro h q hqle
    by_cases hlt : (row.symm q).val < p.val
    · exact h q hlt
    · have heq : row.symm q = p := by
        apply le_antisymm
        · exact hqle
        · exact le_of_not_gt hlt
      have hq : q = c := by
        calc
          q = row (row.symm q) := (Equiv.apply_symm_apply row q).symm
          _ = row p := by rw [heq]
          _ = c := hrowp
      rw [hq]
      exact fixpoint_balanced_c_not_coverable α' c A B hfix hmid hAB


/-! ## Pass-history: how the row-`< p` words were produced

The classical no-reappearance claim is a statement about states obtained from
a residual state by the *actual pass* at the balanced coordinate `c` (own
word `A ++ B`, `|A| = |B|`).  A pass move acts on **one coordinate only**
(`w_q ↦ w_q · w_p⁻¹` when `w_q` ends with `B` — the *ends-move*; `w_q ↦
w_p · w_q` when `w_q` begins with `B⁻¹` = `invRev B` — the *begins-move*),
and `c` itself never moves, so its word `A ++ B` is constant throughout the
pass.  Consequently the *pass-history of a single coordinate* is a purely
word-level trajectory: its word is transformed by the two moves relative to
the fixed halves `A B`, and all other coordinates' words are untouched.

This section defines that infrastructure:

* `WordPassFixed B w` — `w` is in neither pass class (does not end with `B`,
  does not begin with `invRev B`): the per-coordinate content of the fixpoint
  predicate `NoPassActive`;

`PassWordMove` permits a move whenever its source has the corresponding
shape; the run's own deterministic ends-priority scheduling (an ends-move
when the word ends with `B`, else a begins-move when it begins with `B⁻¹`) is
a special case, so `PassWordHistory` describes a *superset* of the words an
actual run can produce — the safe direction: any property proved for every
history-reachable word holds for the actual post-pass words.
* `PassWordMove A B` — one pass move on a word (ends: source `Y ++ B`,
  target `reduce (Y ++ invRev A)`; begins: source `invRev B ++ X`, target
  `reduce (A ++ X)`), matching the automorphism moves exactly
  (`mul w (inv w_p)` resp. `mul w_p w` — the cancelled `B · invRev B` /
  `B⁻¹ · B` middle is fully absorbed by reduction);
* `PassWordHistory A B w₀ w₁` — `w₁` is reachable from `w₀` by a sequence of
  pass moves (`Relation.ReflTransGen`);
* `PassHistoryState α α' c A B` — every coordinate `q ≠ c` of `α'` has
  pass-history from its `α`-word, and `c`'s word is unchanged;
* `PassHistoryRow α α' c A B row p` — the same restricted to the row-`< p`
  coordinates (plus `c` fixed): the shape consumed by the `i < p` argument.

API lemmas: single-step histories (`passWordHistory_ends`/`_begins`), the
trivial history (`passWordHistory_refl`), the **fixpoint lemma** (`a word in
neither class admits only the trivial history` — `passWordHistory_eq_of_fixed`),
and the characterisation of `NoPassActive` per coordinate
(`noPassActive_iff_all_fixed`).  All kernel-checked; axioms
`[propext, Classical.choice, Quot.sound]`. -/

/-- The word `w` is in neither pass class of the fixpoint predicate: it does
not end with the second half `B` and does not begin with its inverse
`invRev B`. -/
def WordPassFixed {α : Type*} [DecidableEq α] (B : List (α × Bool))
    (w : List (α × Bool)) : Prop :=
  (¬ ∃ Y : List (α × Bool), w = Y ++ B) ∧
    (¬ ∃ X : List (α × Bool), w = FreeGroup.invRev B ++ X)

/-- One pass move on the word of a non-balanced coordinate, relative to the
balanced coordinate's fixed halves `A B` (word `A ++ B`): the *ends-move*
(source `w = Y ++ B`, replacing the `B`-suffix by `invRev A`) or the
*begins-move* (source `w = invRev B ++ X`, replacing the `B⁻¹`-prefix by
`A`).  These are exactly the word effects of right composition by `rhoNeg`
resp. `lam` with the balanced coordinate (the cancelled `B · invRev B` /
`invRev B · B` middles reduce away). -/
def PassWordMove {α : Type*} [DecidableEq α] (A B : List (α × Bool))
    (w w' : List (α × Bool)) : Prop :=
  (∃ Y : List (α × Bool), w = Y ++ B ∧ w' = FreeGroup.reduce (Y ++ FreeGroup.invRev A)) ∨
    (∃ X : List (α × Bool), w = FreeGroup.invRev B ++ X ∧ w' = FreeGroup.reduce (A ++ X))

/-- The word `w₁` arises from `w₀` by a sequence of pass moves (possibly
empty) at the balanced halves `A B`. -/
def PassWordHistory {α : Type*} [DecidableEq α] (A B : List (α × Bool))
    (w₀ w₁ : List (α × Bool)) : Prop :=
  Relation.ReflTransGen (PassWordMove A B) w₀ w₁

/-- The word `w₁` arises from `w₀` by at least one pass move. -/
def PassWordMoved {α : Type*} [DecidableEq α] (A B : List (α × Bool))
    (w₀ w₁ : List (α × Bool)) : Prop :=
  Relation.TransGen (PassWordMove A B) w₀ w₁

/-- The trivial (empty) history: every word has pass-history to itself. -/
lemma passWordHistory_refl {α : Type*} [DecidableEq α] (A B : List (α × Bool))
    (w : List (α × Bool)) : PassWordHistory A B w w :=
  Relation.ReflTransGen.refl

/-- A single ends-move is a history. -/
lemma passWordHistory_ends {α : Type*} [DecidableEq α] (A B Y : List (α × Bool)) :
    PassWordHistory A B (Y ++ B) (FreeGroup.reduce (Y ++ FreeGroup.invRev A)) :=
  Relation.ReflTransGen.single (Or.inl ⟨Y, ⟨rfl, rfl⟩⟩)

/-- A single begins-move is a history. -/
lemma passWordHistory_begins {α : Type*} [DecidableEq α] (A B X : List (α × Bool)) :
    PassWordHistory A B (FreeGroup.invRev B ++ X)
      (FreeGroup.reduce (A ++ X)) :=
  Relation.ReflTransGen.single (Or.inr ⟨X, ⟨rfl, rfl⟩⟩)

/-- Histories compose. -/
lemma passWordHistory_trans {α : Type*} [DecidableEq α] (A B : List (α × Bool))
    {w₀ w₁ w₂ : List (α × Bool)} (h01 : PassWordHistory A B w₀ w₁)
    (h12 : PassWordHistory A B w₁ w₂) : PassWordHistory A B w₀ w₂ :=
  Relation.ReflTransGen.trans h01 h12

/-- **Fixpoint lemma.**  A word in neither pass class (`WordPassFixed B w`)
admits only the trivial pass-history: no pass move applies to it, so any
history from it is empty.  (Equivalently: an unchanged row-`< p` word stays
exactly as it was — its coordinate was not combined by the pass.) -/
lemma passWordHistory_eq_of_fixed {α : Type*} [DecidableEq α] (A B : List (α × Bool))
    {w w' : List (α × Bool)} (hfix : WordPassFixed B w)
    (h : PassWordHistory A B w w') : w' = w := by
  induction h with
  | refl => rfl
  | tail hb hstep ih =>
      -- the last step leads out of the intermediate word `b`, which the
      -- induction hypothesis identifies with `w`; but no move applies to `w`
      exfalso
      rw [ih] at hstep
      rcases hstep with ⟨Y, hw, hpost⟩ | ⟨X, hw, hpost⟩
      · exact hfix.1 ⟨Y, hw⟩
      · exact hfix.2 ⟨X, hw⟩

/-- The per-coordinate content of the fixpoint predicate: `NoPassActive`
holds exactly when every coordinate other than `c` has a word in neither pass
class. -/
theorem noPassActive_iff_all_fixed {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (c : Fin n) (A B : List (Fin n × Bool)) :
    NoPassActive α c A B ↔ ∀ u : Fin n, u ≠ c → WordPassFixed B (coordWord α u) := by
  constructor
  · intro hfix u hu
    exact hfix u hu
  · intro hall u hu
    unfold WordPassFixed at hall
    exact hall u hu

/-- **State-level pass-history.**  `α'` is obtained from `α` by the pass at
the balanced coordinate `c` (fixed word `A ++ B`): every coordinate `q ≠ c`
has pass-history from its `α`-word to its `α'`-word, and `c`'s own word is
unchanged. -/
def PassHistoryState {n : ℕ} (α α' : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B : List (Fin n × Bool)) : Prop :=
  (coordWord α' c = coordWord α c) ∧
    ∀ q : Fin n, q ≠ c → PassWordHistory A B (coordWord α q) (coordWord α' q)

/-- **Row-`< p` pass-history.**  `α'` is obtained from `α` by the pass at the
balanced coordinate `c` at row position `p` (fixed word `A ++ B`): `c`'s word
is unchanged and every coordinate at a row position `< p` has pass-history
from its `α`-word to its `α'`-word.  This is the shape of the pass-history
hypothesis the `i < p` argument consumes. -/
def PassHistoryRow {n : ℕ} (α α' : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B : List (Fin n × Bool)) (row : Equiv.Perm (Fin n)) (p : Fin n) : Prop :=
  (coordWord α' c = coordWord α c) ∧
    ∀ q : Fin n, (row.symm q).val < p.val →
      PassWordHistory A B (coordWord α q) (coordWord α' q)

/-- Full-state pass-history implies the row-`< p` restriction (when `c` sits
at row position `p`). -/
theorem passHistoryState_implies_row {n : ℕ} (α α' : MulAut (FreeGroup (Fin n)))
    (c : Fin n) (A B : List (Fin n × Bool)) (row : Equiv.Perm (Fin n)) (p : Fin n)
    (hrowp : row p = c) (h : PassHistoryState α α' c A B) :
    PassHistoryRow α α' c A B row p := by
  constructor
  · exact h.1
  · intro q hq
    apply h.2
    intro hqc
    -- q = c would sit at row position p, contradicting `row position < p`
    have hpos : (row.symm c).val = p.val := by
      calc
        (row.symm c).val = (row.symm (row p)).val := by rw [hrowp]
        _ = p.val := by rw [Equiv.symm_apply_apply]
    rw [hqc] at hq
    omega


/-- **No move leaves a fixpoint word.**  A word in neither pass class
(`WordPassFixed B w`) admits no pass move at all (the ends move needs a
`B`-suffix, the begins move an `invRev B`-prefix).  Together with
`passWordHistory_eq_of_fixed` this is the per-coordinate content of "the
fixpoint is reached": once every coordinate's word is fixed, the pass is
over. -/
lemma no_passWordMove_of_fixed {α : Type*} [DecidableEq α] (A B : List (α × Bool))
    {w w' : List (α × Bool)} (hfix : WordPassFixed B w) :
    ¬ PassWordMove A B w w' := by
  intro h
  rcases h with ⟨Y, hw, hpost⟩ | ⟨X, hw, hpost⟩
  · exact hfix.1 ⟨Y, hw⟩
  · exact hfix.2 ⟨X, hw⟩


/-! ## The genuine run bundle (final-form hypothesis container)

The `i < p` no-reappearance theorem is a statement about states obtained from
a **genuine run**: the pre-state is a residual ordered basis whose minimal
exactly-half-absorbed element sits at row `p` with word `A ++ B`
(`|A| = |B|`), and the post-pass automorphism is reached by the executed pass
at `c := S.row p` (rows `< p` have pass-history, the fixpoint
`NoPassActive α' c A B` is reached, and no strict move fired, so `N` is
preserved and the row order is unchanged).

`PassHistoryRow` **alone** (plus the local post-fixpoint hypotheses) is
insufficient — the identity pass makes it trivial, and synthetic
counterexamples exist (`FallTwoRunNotes.md`) — so the theorem must carry this
bundle.  The bundle is infrastructure (a predicate); no claim is made here
that it suffices, and the word theorem itself (`RowStrictPostRun`) is open,
machine-validated for actual executions only. -/

/-- The **genuine run bundle**: the ordered residual basis state `S` (no
strict elementary move: `NoEndCancel`) has its minimal exactly-half-absorbed
element at row position `p`, `c := S.row p` has word `A ++ B` (`|A| = |B|`),
and the post-pass automorphism `α'` is reached from `S.α` by an executed pass
at `c`: every row-`< p` coordinate has pass-history, the fixpoint
(`NoPassActive α' c A B`) is reached, and no strict move fired — so each
coordinate's reduced length is preserved (`per-coordinate norm equality`,
which implies the row order is unchanged and, since every pass move is
non-increasing, that every move is exact: no seam cancellation). -/
def GenuineRunTo {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n))) : Prop :=
  NoEndCancel n S.α ∧ ExactlyHalfAbsorbed S p ∧
    (∀ i : Fin n, i.val < p.val → ¬ ExactlyHalfAbsorbed S i) ∧
    (S.α (FreeGroup.of (S.row p))).toWord = A ++ B ∧ A.length = B.length ∧
    PassHistoryState S.α α' (S.row p) A B ∧
    NoPassActive α' (S.row p) A B ∧
    (∀ i : Fin n, FreeGroup.norm (α' (FreeGroup.of (S.row i))) =
      FreeGroup.norm (S.α (FreeGroup.of (S.row i))))

/-- **The `i < p` word theorem (open, final-form container, STRENGTHENED
with post-residual).**  Under a genuine run to a *residual* post-state
`α'` — residual ordered basis pre-state `S` (`NoEndCancel n S.α`), minimal
exactly-half-absorbed row `p`, executed pass at `c` with word `A ++ B`
(fixpoint reached, `N` preserved), and the post-state itself still admits no
strict elementary move (`NoEndCancel n α'`) — no coordinate at a row position
below `p` is two-sidedly coverable: the word-level no-reappearance whose
contrapositive (`coverable_free_not_absorbed`) closes the aggregate
no-reappearance of the Fall-II run.

The post-residual hypothesis is **essential** — the un-strengthened
statement is false at n ≥ 4.  Machine counterexample (n = 4, genuine residual
descent, `/tmp/fg2`): pre-state rows `[A0a1, A0a2, a3A1, a0A1a2]`
(`A0a2` = `a0⁻¹a2`, exactly-half-absorbed at row position `p = 1`, halves
`A0 | a2`; row 0 is not exactly-half-absorbed, so the minimality of `p`
holds), fixpoint pass at `c`; post-state rows `[A0a1, A0a2, a3A1, a0A1a0]`
has per-coordinate norm equality and is `NoPassActive`, but is NOT residual
(the strict move `w0 ↦ w3·w0` shortens `a0⁻¹a1` to `a0`) and its row-`< p`
coordinate `q = 0` (word `A0a1`) IS two-sidedly coverable (right class via
`w3` ending with `a0`, left class via `w2` ending with `A1`, on the
`w⁻¹` orientation).  Since such a non-residual post-state ends the Fall-II
phase by firing the strict move (strict reappearance) instead of advancing
the index, the run only consumes the claim in the residual-post case —
which is exactly the strengthened statement here, and machine-validates
cleanly: 0 violations over ~450 residual post-states at n = 3/4 (`valLow4`).
Its proof mechanism is open; no `sorry`-stated lemma is committed. -/
def RowStrictPostRun {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n))) : Prop :=
  GenuineRunTo S p A B α' → NoEndCancel n α' → RowInvariantStrict α' S.row p


/-! ## Residual states: coverers are not shorter than the covered element

Machine (n = 3, `/tmp/fg2`): in residual states (no strict elementary move,
`NoEndCancel`) every coverer of an even element `q` has reduced length at
least `|q|` (848 coverable even elements, 0 shorter coverers).  This is
provable: a coverer supplies the *factorisation* of one of the products
`w_v^{±1}·w_q`, `w_q·w_u^{±1}` in which the covered half cancels (`invRev A`
against `A`, resp. `B` against `invRev B`), so the product's norm is at most
the coverer's norm — while `NoEndCancel` bounds the product below by `|w_q|`.
The group-level cancellation is `mk`-calculus (`mul_mk`, `inv_mk`,
`mk_mul_cancel_center`); the word-level telescoping helpers
(`reduce_concat_cancel_middle`, `reduce_concat_length_cancel_middle`,
`reduce_append_invRev_right`) live in the shared commons
(`Commons.GroupTheory.FreeGroup`). -/

/-- The group identity behind the coverer bounds: a factor `C` multiplied
with its inverse-reversal cancels in the middle of a product. -/
private lemma mk_mul_cancel_center {α : Type*} (U C V : List (α × Bool)) :
    (FreeGroup.mk U * FreeGroup.mk C) *
        (FreeGroup.mk (FreeGroup.invRev C) * FreeGroup.mk V) =
      FreeGroup.mk U * FreeGroup.mk V := by
  rw [← FreeGroup.inv_mk]
  group

/-- `norm (mk U * mk V) ≤ |U| + |V|`. -/
private lemma norm_mk_mul_le {α : Type*} [DecidableEq α] (U V : List (α × Bool)) :
    FreeGroup.norm (FreeGroup.mk U * FreeGroup.mk V) ≤ U.length + V.length := by
  have h := FreeGroup.norm_mul_le (x := FreeGroup.mk U) (y := FreeGroup.mk V)
  have hU : FreeGroup.norm (FreeGroup.mk U) ≤ U.length := by
    change (FreeGroup.mk U).toWord.length ≤ U.length
    rw [FreeGroup.toWord_mk]
    exact FreeGroup.Red.length_le (FreeGroup.reduce.red (L := U))
  have hV : FreeGroup.norm (FreeGroup.mk V) ≤ V.length := by
    change (FreeGroup.mk V).toWord.length ≤ V.length
    rw [FreeGroup.toWord_mk]
    exact FreeGroup.Red.length_le (FreeGroup.reduce.red (L := V))
  exact le_trans h (add_le_add hU hV)

/-- Coverer bound, left ends-mode: `w_v` ends with `invRev A` (`w_q` begins
with `A`) ⟹ `|w_v·w_q| ≤ |w_v|`. -/
private lemma left_ends_product_le {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    {q v : Fin n} (A B Y : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hq : (α (FreeGroup.of q)).toWord = A ++ B)
    (hY : (α (FreeGroup.of v)).toWord = Y ++ FreeGroup.invRev A) :
    FreeGroup.norm ((α (FreeGroup.of v)) * (α (FreeGroup.of q))) ≤
      FreeGroup.norm (α (FreeGroup.of v)) := by
  have hEq : (α (FreeGroup.of v)) * (α (FreeGroup.of q)) =
      FreeGroup.mk Y * FreeGroup.mk B := by
    calc
      (α (FreeGroup.of v)) * (α (FreeGroup.of q))
          = FreeGroup.mk (Y ++ FreeGroup.invRev A) * FreeGroup.mk (A ++ B) := by
              rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of v)), hY,
                  ← FreeGroup.mk_toWord (x := α (FreeGroup.of q)), hq]
      _ = FreeGroup.mk Y * FreeGroup.mk B := by
              simpa [FreeGroup.invRev_invRev, ← FreeGroup.mul_mk] using
                (mk_mul_cancel_center (U := Y) (C := FreeGroup.invRev A) (V := B))
  calc
    FreeGroup.norm ((α (FreeGroup.of v)) * (α (FreeGroup.of q)))
        = FreeGroup.norm (FreeGroup.mk Y * FreeGroup.mk B) := by rw [hEq]
    _ ≤ Y.length + B.length := norm_mk_mul_le Y B
    _ = FreeGroup.norm (α (FreeGroup.of v)) := by
        rw [show FreeGroup.norm (α (FreeGroup.of v)) =
              (α (FreeGroup.of v)).toWord.length by rfl]
        rw [hY, List.length_append, FreeGroup.invRev_length, hAB]

/-- Coverer bound, left begins-mode: `w_v` begins with `A` ⟹
`|w_v⁻¹·w_q| ≤ |w_v|`. -/
private lemma left_begins_product_le {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    {q v : Fin n} (A B W : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hq : (α (FreeGroup.of q)).toWord = A ++ B)
    (hW : (α (FreeGroup.of v)).toWord = A ++ W) :
    FreeGroup.norm ((α (FreeGroup.of v))⁻¹ * (α (FreeGroup.of q))) ≤
      FreeGroup.norm (α (FreeGroup.of v)) := by
  have hEq : (α (FreeGroup.of v))⁻¹ * (α (FreeGroup.of q)) =
      FreeGroup.mk (FreeGroup.invRev W) * FreeGroup.mk B := by
    calc
      (α (FreeGroup.of v))⁻¹ * (α (FreeGroup.of q))
          = (FreeGroup.mk (A ++ W))⁻¹ * FreeGroup.mk (A ++ B) := by
              rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of v)), hW,
                  ← FreeGroup.mk_toWord (x := α (FreeGroup.of q)), hq]
      _ = FreeGroup.mk (FreeGroup.invRev W ++ FreeGroup.invRev A) *
            FreeGroup.mk (A ++ B) := by
              rw [FreeGroup.inv_mk, FreeGroup.invRev_append]
      _ = FreeGroup.mk (FreeGroup.invRev W) * FreeGroup.mk B := by
              rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
              simpa [FreeGroup.invRev_invRev] using
                (mk_mul_cancel_center (U := FreeGroup.invRev W) (C := FreeGroup.invRev A)
                  (V := B))
  calc
    FreeGroup.norm ((α (FreeGroup.of v))⁻¹ * (α (FreeGroup.of q)))
        = FreeGroup.norm (FreeGroup.mk (FreeGroup.invRev W) * FreeGroup.mk B) := by rw [hEq]
    _ ≤ (FreeGroup.invRev W).length + B.length := norm_mk_mul_le (FreeGroup.invRev W) B
    _ = FreeGroup.norm (α (FreeGroup.of v)) := by
        rw [show FreeGroup.norm (α (FreeGroup.of v)) =
              (α (FreeGroup.of v)).toWord.length by rfl]
        rw [hW, List.length_append, FreeGroup.invRev_length, hAB]
        omega

/-- Coverer bound, right ends-mode: `w_u` ends with `B` (`w_q` ends with
`B`) ⟹ `|w_q·w_u⁻¹| ≤ |w_u|`. -/
private lemma right_ends_product_le {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    {q u : Fin n} (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hq : (α (FreeGroup.of q)).toWord = A ++ B)
    (hZ : (α (FreeGroup.of u)).toWord = Z ++ B) :
    FreeGroup.norm ((α (FreeGroup.of q)) * (α (FreeGroup.of u))⁻¹) ≤
      FreeGroup.norm (α (FreeGroup.of u)) := by
  have hEq : (α (FreeGroup.of q)) * (α (FreeGroup.of u))⁻¹ =
      FreeGroup.mk A * FreeGroup.mk (FreeGroup.invRev Z) := by
    calc
      (α (FreeGroup.of q)) * (α (FreeGroup.of u))⁻¹
          = FreeGroup.mk (A ++ B) * (FreeGroup.mk (Z ++ B))⁻¹ := by
              rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of q)), hq,
                  ← FreeGroup.mk_toWord (x := α (FreeGroup.of u)), hZ]
      _ = FreeGroup.mk (A ++ B) * FreeGroup.mk (FreeGroup.invRev B ++ FreeGroup.invRev Z) := by
              rw [FreeGroup.inv_mk, FreeGroup.invRev_append]
      _ = FreeGroup.mk A * FreeGroup.mk (FreeGroup.invRev Z) := by
              rw [← FreeGroup.mul_mk]
              simpa [FreeGroup.invRev_invRev, ← FreeGroup.mul_mk] using
                (mk_mul_cancel_center (U := A) (C := B) (V := FreeGroup.invRev Z))
  calc
    FreeGroup.norm ((α (FreeGroup.of q)) * (α (FreeGroup.of u))⁻¹)
        = FreeGroup.norm (FreeGroup.mk A * FreeGroup.mk (FreeGroup.invRev Z)) := by rw [hEq]
    _ ≤ A.length + (FreeGroup.invRev Z).length := norm_mk_mul_le A (FreeGroup.invRev Z)
    _ = FreeGroup.norm (α (FreeGroup.of u)) := by
        rw [show FreeGroup.norm (α (FreeGroup.of u)) =
              (α (FreeGroup.of u)).toWord.length by rfl]
        rw [hZ, List.length_append, FreeGroup.invRev_length, hAB]
        omega

/-- Coverer bound, right begins-mode: `w_u` begins with `invRev B` ⟹
`|w_q·w_u| ≤ |w_u|`. -/
private lemma right_begins_product_le {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    {q u : Fin n} (A B W : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hq : (α (FreeGroup.of q)).toWord = A ++ B)
    (hW : (α (FreeGroup.of u)).toWord = FreeGroup.invRev B ++ W) :
    FreeGroup.norm ((α (FreeGroup.of q)) * (α (FreeGroup.of u))) ≤
      FreeGroup.norm (α (FreeGroup.of u)) := by
  have hEq : (α (FreeGroup.of q)) * (α (FreeGroup.of u)) =
      FreeGroup.mk A * FreeGroup.mk W := by
    calc
      (α (FreeGroup.of q)) * (α (FreeGroup.of u))
          = FreeGroup.mk (A ++ B) * FreeGroup.mk (FreeGroup.invRev B ++ W) := by
              rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of q)), hq,
                  ← FreeGroup.mk_toWord (x := α (FreeGroup.of u)), hW]
      _ = FreeGroup.mk A * FreeGroup.mk W := by
              rw [← FreeGroup.mul_mk]
              simpa [FreeGroup.invRev_invRev, ← FreeGroup.mul_mk] using
                (mk_mul_cancel_center (U := A) (C := B) (V := W))
  calc
    FreeGroup.norm ((α (FreeGroup.of q)) * (α (FreeGroup.of u)))
        = FreeGroup.norm (FreeGroup.mk A * FreeGroup.mk W) := by rw [hEq]
    _ ≤ A.length + W.length := norm_mk_mul_le A W
    _ = FreeGroup.norm (α (FreeGroup.of u)) := by
        rw [show FreeGroup.norm (α (FreeGroup.of u)) =
              (α (FreeGroup.of u)).toWord.length by rfl]
        rw [hW, List.length_append, FreeGroup.invRev_length, hAB]

/-! ## The residual coverer-length theorems -/

/-- **Residual left ends-coverer is not shorter.**  In a residual state
(`NoEndCancel`), if `w_v` ends with `invRev A` and the even element `q` has
word `A ++ B` (`|A| = |B|`), then `|w_v| ≥ |w_q|`. -/
theorem residual_left_ends_member_ge {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {q v : Fin n} (hqv : v ≠ q)
    (A B Y : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hq : (α (FreeGroup.of q)).toWord = A ++ B)
    (hY : (α (FreeGroup.of v)).toWord = Y ++ FreeGroup.invRev A) :
    FreeGroup.norm (α (FreeGroup.of v)) ≥ FreeGroup.norm (α (FreeGroup.of q)) := by
  have hlo : FreeGroup.norm (α (FreeGroup.of q)) ≤
      FreeGroup.norm ((α (FreeGroup.of v)) * (α (FreeGroup.of q))) := (hres q v hqv.symm).2.2.2
  exact le_trans hlo (left_ends_product_le α (A := A) (B := B) (Y := Y) hAB hq hY)

/-- **Residual left begins-coverer is not shorter.**  If `w_v` begins with
`A` then `|w_v| ≥ |w_q|` in a residual state. -/
theorem residual_left_begins_member_ge {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {q v : Fin n} (hqv : v ≠ q)
    (A B W : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hq : (α (FreeGroup.of q)).toWord = A ++ B)
    (hW : (α (FreeGroup.of v)).toWord = A ++ W) :
    FreeGroup.norm (α (FreeGroup.of v)) ≥ FreeGroup.norm (α (FreeGroup.of q)) := by
  have hlo : FreeGroup.norm (α (FreeGroup.of q)) ≤
      FreeGroup.norm ((α (FreeGroup.of v))⁻¹ * (α (FreeGroup.of q))) := (hres q v hqv.symm).2.2.1
  exact le_trans hlo (left_begins_product_le α (A := A) (B := B) (W := W) hAB hq hW)

/-- **Residual right ends-coverer is not shorter.**  If `w_u` ends with `B`
then `|w_u| ≥ |w_q|` in a residual state. -/
theorem residual_right_ends_member_ge {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {q u : Fin n} (hqu : u ≠ q)
    (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hq : (α (FreeGroup.of q)).toWord = A ++ B)
    (hZ : (α (FreeGroup.of u)).toWord = Z ++ B) :
    FreeGroup.norm (α (FreeGroup.of u)) ≥ FreeGroup.norm (α (FreeGroup.of q)) := by
  have hlo : FreeGroup.norm (α (FreeGroup.of q)) ≤
      FreeGroup.norm ((α (FreeGroup.of q)) * (α (FreeGroup.of u))⁻¹) := (hres q u hqu.symm).1
  exact le_trans hlo (right_ends_product_le α (A := A) (B := B) (Z := Z) hAB hq hZ)

/-- **Residual right begins-coverer is not shorter.**  If `w_u` begins with
`invRev B` then `|w_u| ≥ |w_q|` in a residual state. -/
theorem residual_right_begins_member_ge {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {q u : Fin n} (hqu : u ≠ q)
    (A B W : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hq : (α (FreeGroup.of q)).toWord = A ++ B)
    (hW : (α (FreeGroup.of u)).toWord = FreeGroup.invRev B ++ W) :
    FreeGroup.norm (α (FreeGroup.of u)) ≥ FreeGroup.norm (α (FreeGroup.of q)) := by
  have hlo : FreeGroup.norm (α (FreeGroup.of q)) ≤
      FreeGroup.norm ((α (FreeGroup.of q)) * (α (FreeGroup.of u))) := (hres q u hqu.symm).2.1
  exact le_trans hlo (right_begins_product_le α (A := A) (B := B) (W := W) hAB hq hW)

/-- A member of the left covering class of an even element of a residual
state is not shorter than the element (either covering mode). -/
theorem residual_left_class_member_ge {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {q v : Fin n} (hqv : v ≠ q)
    (A B : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hq : (α (FreeGroup.of q)).toWord = A ++ B)
    (hm : EndsWithWord (coordWord α v) (FreeGroup.invRev A) ∨
      BeginsWithWord (coordWord α v) A) :
    FreeGroup.norm (α (FreeGroup.of v)) ≥ FreeGroup.norm (α (FreeGroup.of q)) := by
  rcases hm with hE | hB
  · rcases hE with ⟨Y, hY⟩
    exact residual_left_ends_member_ge α hres hqv (A := A) (B := B) (Y := Y) hAB hq
      (by simpa [coordWord] using hY)
  · rcases hB with ⟨W, hW⟩
    exact residual_left_begins_member_ge α hres hqv (A := A) (B := B) (W := W) hAB hq
      (by simpa [coordWord] using hW)

/-- A member of the right covering class of an even element of a residual
state is not shorter than the element (either covering mode). -/
theorem residual_right_class_member_ge {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {q u : Fin n} (hqu : u ≠ q)
    (A B : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hq : (α (FreeGroup.of q)).toWord = A ++ B)
    (hm : EndsWithWord (coordWord α u) B ∨ BeginsWithWord (coordWord α u) (FreeGroup.invRev B)) :
    FreeGroup.norm (α (FreeGroup.of u)) ≥ FreeGroup.norm (α (FreeGroup.of q)) := by
  rcases hm with hE | hB
  · rcases hE with ⟨Z, hZ⟩
    exact residual_right_ends_member_ge α hres hqu (A := A) (B := B) (Z := Z) hAB hq
      (by simpa [coordWord] using hZ)
  · rcases hB with ⟨W, hW⟩
    exact residual_right_begins_member_ge α hres hqu (A := A) (B := B) (W := W) hAB hq
      (by simpa [coordWord] using hW)

/-- **Left covering implies a long-enough coverer.**  If the left covering
class of the even element `q` (word `A ++ B`, `|A| = |B|`) is inhabited in a
residual state, some coordinate `v ≠ q` has `|w_v| ≥ |w_q|`. -/
theorem residual_left_cover_ge {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {q : Fin n} (A B : List (Fin n × Bool))
    (hAB : A.length = B.length) (hq : (α (FreeGroup.of q)).toWord = A ++ B)
    (hLC : LeftCoverClass α q A) :
    ∃ v : Fin n, v ≠ q ∧
      FreeGroup.norm (α (FreeGroup.of v)) ≥ FreeGroup.norm (α (FreeGroup.of q)) := by
  rcases hLC with ⟨v, hqv, hm⟩
  exact ⟨v, hqv, residual_left_class_member_ge α hres hqv A B hAB hq hm⟩

/-- **Right covering implies a long-enough coverer.**  If the right covering
class of the even element `q` is inhabited in a residual state, some
coordinate `u ≠ q` has `|w_u| ≥ |w_q|`. -/
theorem residual_right_cover_ge {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {q : Fin n} (A B : List (Fin n × Bool))
    (hAB : A.length = B.length) (hq : (α (FreeGroup.of q)).toWord = A ++ B)
    (hRC : RightCoverClass α q B) :
    ∃ u : Fin n, u ≠ q ∧
      FreeGroup.norm (α (FreeGroup.of u)) ≥ FreeGroup.norm (α (FreeGroup.of q)) := by
  rcases hRC with ⟨u, hqu, hm⟩
  exact ⟨u, hqu, residual_right_class_member_ge α hres hqu A B hAB hq hm⟩


/-! ## Excess-short junctions shorten strictly (Conjecture-K fragment)

`Conjecture K` (machine-validated, open) asserts that every balanced
(`FallTwoConfig` / `ExactlyHalfAbsorbed`) configuration of half-length
`k ≥ 2` admits a strict elementary move.  Its clean provable fragment is the
**excess-short junction**: if the covering neighbour on the left has word
`Y ++ invRev A` (`w_q`'s own word is `A ++ B`) with the *excess* `Y` shorter
than the half `A` (`|Y| < |A|`), then multiplying `w_q` on the left by the
coverer shortens it strictly: `|g·w_q| < |w_q|` — the `A^{-1}`-suffix of the
coverer cancels the whole first half `A`, leaving at most `Y ++ B`
(`|Y| + |B| < |A| + |B| = |w_q|`).  The right-handed mirror is the same
through `B·B^{-1}`.  Machine: of 46 machine-found `k ≥ 2` balanced rows,
44 have a witness with an excess-short side and these two theorems give the
strict move on `w_q`; the remaining rows need the global aggregate structure
(the local covering triple alone does not force a move — machine
counterexample triples exist) and stay open.

The sign-free formulation (an *element* `g` whose word is the coverer word)
subsumes both factor orientations `g = ± w_v`: each such `g` attaches to one
of the four elementary moves (`lam`/`lamNeg`/`rho`/`rhoNeg`) on `w_q`. -/

/-- **Excess-short left junction.**  If the element `g` has reduced word
`Y ++ invRev A` and the element `w_q` has word `A ++ B` with the excess `Y`
shorter than the half `A`, then left multiplication by `g` shortens `w_q`
strictly: `|g·w_q| < |w_q|`. -/
theorem excessLeftShortens {α : Type*} [DecidableEq α] (A B Y : List (α × Bool))
    (w : FreeGroup α) (hw : w.toWord = A ++ B)
    (g : FreeGroup α) (hg : g.toWord = Y ++ FreeGroup.invRev A)
    (hshort : Y.length < A.length) :
    FreeGroup.norm (g * w) < FreeGroup.norm w := by
  have hEq : g * w = FreeGroup.mk Y * FreeGroup.mk B := by
    calc
      g * w = FreeGroup.mk (Y ++ FreeGroup.invRev A) * FreeGroup.mk (A ++ B) := by
              rw [← FreeGroup.mk_toWord (x := g), hg, ← FreeGroup.mk_toWord (x := w), hw]
      _ = FreeGroup.mk Y * FreeGroup.mk B := by
              simpa [FreeGroup.invRev_invRev, ← FreeGroup.mul_mk] using
                (mk_mul_cancel_center (U := Y) (C := FreeGroup.invRev A) (V := B))
  calc
    FreeGroup.norm (g * w) = FreeGroup.norm (FreeGroup.mk Y * FreeGroup.mk B) := by rw [hEq]
    _ ≤ Y.length + B.length := norm_mk_mul_le Y B
    _ < FreeGroup.norm w := by
        rw [show FreeGroup.norm w = w.toWord.length by rfl]
        rw [hw]
        simp
        exact hshort

/-- **Excess-short right junction.**  If the element `g` has reduced word
`invRev B ++ Z` and the element `w_q` has word `A ++ B` with the excess `Z`
shorter than the half `B`, then right multiplication by `g` shortens `w_q`
strictly: `|w_q·g| < |w_q|`. -/
theorem excessRightShortens {α : Type*} [DecidableEq α] (A B Z : List (α × Bool))
    (w : FreeGroup α) (hw : w.toWord = A ++ B)
    (g : FreeGroup α) (hg : g.toWord = FreeGroup.invRev B ++ Z)
    (hshort : Z.length < B.length) :
    FreeGroup.norm (w * g) < FreeGroup.norm w := by
  have hEq : w * g = FreeGroup.mk A * FreeGroup.mk Z := by
    calc
      w * g = FreeGroup.mk (A ++ B) * FreeGroup.mk (FreeGroup.invRev B ++ Z) := by
              rw [← FreeGroup.mk_toWord (x := w), hw, ← FreeGroup.mk_toWord (x := g), hg]
      _ = FreeGroup.mk A * FreeGroup.mk Z := by
              simpa [FreeGroup.invRev_invRev, ← FreeGroup.mul_mk] using
                (mk_mul_cancel_center (U := A) (C := B) (V := Z))
  calc
    FreeGroup.norm (w * g) = FreeGroup.norm (FreeGroup.mk A * FreeGroup.mk Z) := by rw [hEq]
    _ ≤ A.length + Z.length := norm_mk_mul_le A Z
    _ < FreeGroup.norm w := by
        rw [show FreeGroup.norm w = w.toWord.length by rfl]
        rw [hw]
        simp
        exact hshort


/-! ## The post-state half, first lemma: what a non-cancelling pass move
produces

The doubly-private-empty-side mechanism needs the *form content of the pass
moves*: in a genuine run no strict move fires, so every pass move is
length-preserving — equivalently, the introduced segment does not cancel at
its seam.  A non-cancelling *ends*-move (`w = Y ++ B` ↦ `reduce (Y ++
invRev A)`) produces exactly `Y ++ invRev A`, whose new suffix is
`invRev A`; a non-cancelling *begins*-move (`w = invRev B ++ X` ↦
`reduce (A ++ X)`) produces exactly `A ++ X`, whose new prefix is `A`.  So
every new short suffix of a combined word comes from `invRev A_p` and every
new short prefix from `A_p` — the single-move content behind the form
property (`beginAp` / `endInv`) that the low-row deficiency pattern is built
on. -/

/-- A non-cancelling ends-move result is the exact concatenation
`Y ++ invRev A`, ending with `invRev A`. -/
theorem endsMove_no_cancel_form {α : Type*} [DecidableEq α]
    (A B Y : List (α × Bool))
    (hred : FreeGroup.IsReduced (Y ++ FreeGroup.invRev A)) :
    FreeGroup.reduce (Y ++ FreeGroup.invRev A) = Y ++ FreeGroup.invRev A ∧
      EndsWithWord (FreeGroup.reduce (Y ++ FreeGroup.invRev A)) (FreeGroup.invRev A) := by
  have hrv : FreeGroup.reduce (Y ++ FreeGroup.invRev A) = Y ++ FreeGroup.invRev A :=
    FreeGroup.isReduced_iff_reduce_eq.mp hred
  constructor
  · exact hrv
  · rw [hrv]
    unfold EndsWithWord
    exact ⟨Y, rfl⟩

/-- A non-cancelling begins-move result is the exact concatenation `A ++ X`,
beginning with `A`. -/
theorem beginsMove_no_cancel_form {α : Type*} [DecidableEq α]
    (A B X : List (α × Bool))
    (hred : FreeGroup.IsReduced (A ++ X)) :
    FreeGroup.reduce (A ++ X) = A ++ X ∧
      BeginsWithWord (FreeGroup.reduce (A ++ X)) A := by
  have hrv : FreeGroup.reduce (A ++ X) = A ++ X :=
    FreeGroup.isReduced_iff_reduce_eq.mp hred
  constructor
  · exact hrv
  · rw [hrv]
    unfold BeginsWithWord
    exact ⟨X, rfl⟩


/-- Dropping past a prefix: `(Y ++ S)` with `|Y| + m` letters removed leaves
`S` with `m` removed (the prefix `Y` is entirely dropped). -/
private lemma drop_append_past_prefix {α : Type*} (Y S : List α) (m : ℕ) :
    (Y ++ S).drop (Y.length + m) = S.drop m := by
  induction Y generalizing m with
  | nil => simp
  | cons a Y ih =>
      rw [List.length_cons, List.cons_append]
      have hidx : Y.length + 1 + m = (Y.length + m) + 1 := by omega
      rw [hidx, List.drop_succ_cons]
      exact ih m

/-- The length-`r` suffix of a concatenation `Y ++ S` (for `r <= |S|`) is the
length-`r` suffix of `S`: the trailing segment of a word is unaffected by its
prefix. -/
lemma drop_suffix_of_append {α : Type*} (Y S : List α) (r : ℕ) (hr : r ≤ S.length) :
    (Y ++ S).drop ((Y ++ S).length - r) = S.drop (S.length - r) := by
  have hsum : (Y ++ S).length - r = Y.length + (S.length - r) := by
    rw [List.length_append]
    omega
  rw [hsum]
  exact drop_append_past_prefix Y S (S.length - r)

/-- If a word ends with `S`, its length-`r` suffix (`r <= |S|`) is the
length-`r` suffix of `S`.  Applied to an ends-moved word (ending with
`invRev A`), this says every short suffix of the moved word is a suffix of
`invRev A` — the new short endings a pass can create all come from
`invRev A`. -/
lemma suffix_of_EndsWithWord {α : Type*} (W S : List (α × Bool)) (r : ℕ)
    (hr : r ≤ S.length) (hE : EndsWithWord W S) :
    W.drop (W.length - r) = S.drop (S.length - r) := by
  rcases hE with ⟨Y, hW⟩
  rw [hW]
  exact drop_suffix_of_append Y S r hr

/-- **History-level form (ends).**  If the *last* pass move of a coordinate's
history is an ends-move with an exact (non-cancelling) seam, the final word
ends with `invRev A` — the earlier moves are irrelevant to the final form. -/
theorem passWordHistory_lastEnds_form {α : Type*} [DecidableEq α]
    (A B : List (α × Bool)) {w w' : List (α × Bool)}
    (hLast : ∃ s : List (α × Bool), PassWordHistory A B w s ∧
      (∃ Y : List (α × Bool), s = Y ++ B ∧
        w' = FreeGroup.reduce (Y ++ FreeGroup.invRev A) ∧
        FreeGroup.IsReduced (Y ++ FreeGroup.invRev A))) :
    EndsWithWord w' (FreeGroup.invRev A) := by
  rcases hLast with ⟨s, hs, Y, hsY, hpost, hred⟩
  rw [hpost]
  exact (endsMove_no_cancel_form A B Y hred).2

/-- **History-level form (begins).**  If the *last* pass move of a
coordinate's history is a begins-move with an exact (non-cancelling) seam,
the final word begins with `A`. -/
theorem passWordHistory_lastBegins_form {α : Type*} [DecidableEq α]
    (A B : List (α × Bool)) {w w' : List (α × Bool)}
    (hLast : ∃ s : List (α × Bool), PassWordHistory A B w s ∧
      (∃ X : List (α × Bool), s = FreeGroup.invRev B ++ X ∧
        w' = FreeGroup.reduce (A ++ X) ∧
        FreeGroup.IsReduced (A ++ X))) :
    BeginsWithWord w' A := by
  rcases hLast with ⟨s, hs, X, hsX, hpost, hred⟩
  rw [hpost]
  exact (beginsMove_no_cancel_form A B X hred).2


/-! ## First subcase of the "low half is not a new segment" lemma

The low-row deficiency pattern (`beginAp` words have the right class of the
second half empty; `endInv` words the left class of the first half) will
follow once one proves that the low halves are **not fresh segments**: for a
row-`< p` even `beginAp` word `q = A_p ++ X` of length `2k` (`|X| = k`), the
second half `X` is not a suffix of `invRev A_p`; for an `endInv` word of
length `2k`, the first half is not a prefix of `A_p`.  The boundary subcase
(`|q| = 2k`) is a pure reducedness fact: a reduced word never has its second
half equal to the inverse-reversal of its first half (`A ++ invRev A`
cancels completely), proved below; the interior subcase (`|q| < 2k`, proper
suffixes/prefixes) is machine-validated for actual runs but not yet observed
in small samples and not yet proved. -/

/-- `A ++ invRev A` is never reduced (for nonempty `A`): the first half
cancels against the inverse-reversal of itself. -/
lemma not_reduced_append_invRev {α : Type*} [DecidableEq α]
    (A : List (α × Bool)) (hA : A ≠ []) :
    ¬ FreeGroup.IsReduced (A ++ FreeGroup.invRev A) := by
  intro hred
  have hrv : FreeGroup.reduce (A ++ FreeGroup.invRev A) = A ++ FreeGroup.invRev A :=
    FreeGroup.isReduced_iff_reduce_eq.mp hred
  have hrc : FreeGroup.reduce (A ++ FreeGroup.invRev A) = [] :=
    reduce_append_invRev_right A
  have hne : A ++ FreeGroup.invRev A ≠ ([] : List (α × Bool)) := by
    intro hz
    have hpos : 0 < (A ++ FreeGroup.invRev A).length := by
      rw [List.length_append, FreeGroup.invRev_length]
      have hApos : 0 < A.length := by
        cases A with
        | nil => exact False.elim (hA rfl)
        | cons a t => simp
      omega
    have hzlen : (A ++ FreeGroup.invRev A).length = 0 := by
      rw [hz]
      rfl
    omega
  exact hne (hrc.symm.trans hrv).symm

/-- **Boundary subcase.**  A reduced word `A ++ X` with `|A| = |X|` never has
its second half equal to the inverse-reversal of its first half
(`X ≠ invRev A`): otherwise `A ++ invRev A = A ++ X` would be reduced, but it
fully cancels.  For a row-`< p` `beginAp` word of length `2|A_p|` this says
its second half is not the (length-`k`) suffix of `invRev A_p`. -/
theorem reduced_not_invRev_second_half {α : Type*} [DecidableEq α]
    (A X : List (α × Bool)) (hA : A ≠ []) (hred : FreeGroup.IsReduced (A ++ X))
    (hlen : A.length = X.length) : X ≠ FreeGroup.invRev A := by
  intro hX
  apply not_reduced_append_invRev A hA
  rwa [← hX]


/-- **The `beginAp` obstruction (full pass-level form; open).**  In a genuine
run to the fixpoint state at the balanced coordinate `c` (word `A ++ B`,
`|A| = |B|`), let the coordinate `q ≠ c` sit at a row position below `p`
with an even word of the `beginAp` form `A ++ X` (it begins with `A`).  The
claim: the **second half of `q` is not a suffix of `invRev A`** — so no
segment the pass can newly create (ends-moved words end with `invRev A`;
begins-moved words begin with `A`, hence begin with the inverse of the half
only if the half is such a suffix) equals it, and the right covering class
of `q` stays empty (the `beginAp` half of the doubly-private-empty-side
pattern).

Subcase status: the boundary case `|q| = 2|A|` is PROVEN
(`reduced_not_invRev_second_half`: the second half `X` equals the whole
`invRev A`, which would make `A ++ X = A ++ invRev A` non-reduced); the
interior case `|q| < 2|A|` (proper suffixes of `invRev A`) is not
machine-validated at `|A| >= 2` (no such phases found in random sampling)
and not proved.  Open — no `sorry`-stated version is committed. -/
def beginApObstruction {n : ℕ} (α' : MulAut (FreeGroup (Fin n)))
    (c : Fin n) (A B : List (Fin n × Bool)) (row : Equiv.Perm (Fin n))
    (p q : Fin n) (hrowp : row p = c) : Prop :=
  (row.symm q).val < p.val ∧
    (coordWord α' q).length % 2 = 0 ∧
    BeginsWithWord (coordWord α' q) A ∧
    ¬ EndsWithWord (FreeGroup.invRev A) (secondHalf (coordWord α' q))

end Submission.Nielsen


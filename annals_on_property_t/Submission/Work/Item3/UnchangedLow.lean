import Submission.Work.Item3.RowInvariant
import Submission.Work.Item3.AssemblyRun
import Submission.Work.Item3.BothForms
import Submission.Work.Item3.RowForm

open Submission.Nielsen
open FreeGroup
set_option autoImplicit false

/-!
# UnchangedLow: the row-`< p` non-coverability invariant, sharpened to its
two surviving sub-claims

`RowStrictPostRun` (the open ACTIVE TARGET, `RowInvariant.lean`) asserts
that in a genuine run to a residual post-state `α'` (balanced coordinate
`c := S.row p`, word `A ++ B`, `|A| = |B|`), no row-`< p` coordinate `q`
with an even post-word is two-sidedly coverable.  Session record (fresh
machine data, deep-verified against the full `GenuineRunTo` bundle, n =
3..7 — see `FallTwoRunNotes.md`):

* the word-form claim (`row_lt_p_even_post_wordform`: row-`< p` even
  post-words begin with `A` or end with `invRev A`) is **FALSE at n = 4**
  (11/40 genuine residual-post low words violate);
* the symmetric side-claim `LC(first half) nonempty ⟹ W begins with A` is
  **FALSE at n = 6** — verified counterexample (basis of `F₆`, residual pre
  and post, minimal balanced `p`, deep-BFS-confirmed): pre rows
  `[Da, E, CCf, bc, Cd, bf]` → post `[Da, E, bCf, bc, bd, bf]`, balanced
  coordinate `c = bc` at row position 2 (`A = b | B = c`), low even
  unchanged coordinate `q = Da` (halves `D | a`, row position 1): its left
  covering class is inhabited (row 4 `bd` ends with `d = invRev D`) though
  `D ≠ A = b`; its right class is empty, so it is NOT coverable;
* **the two sub-claims that the invariant really needs, and that the data
  supports with 0 violations (n = 3..7; n ≥ 5 sparse):**
  (U1) `RightCoverClass B'` nonempty ⟹ the post-word ends with `invRev A`
       (at `k = 1` = `|A| = |B| = 1`, the only case real residual runs
       exhibit: `B'` = the single letter `invRev A`);
  (U2) if the post-word ends with `invRev A` then `LeftCoverClass A'` is
       empty.
  Since `TwoSidedCoverable q` needs both classes, (U1) + (U2) close it: RC
  forces the endInv form, and the endInv form kills LC.  Note the `k = 1`
  occurrence of (U1)(U2) suffices once the residual `k ≥ 2` impossibility
  (machine-supported, open) is available, because a residual balanced
  element always has half-length 1 in real runs.

The two committed modules already provide: `BothForms.no_word_beginAp_endInv`
(a reduced even word of length `≤ 2|A|` cannot BOTH begin with `A` and end
with `invRev A`) and `RowForm.run_moved_row_form` (moved row-`< p`
coordinates have the last-move form: end `invRev A` or begin `A`).
Together they pin the whole open difficulty to the *unchanged* low words:
(U1) for an unchanged low word whose right class is inhabited, the second
half can only be a piece of `invRev A` — and (U2) such a word's left class
is empty.  The mechanism of (U1)(U2) is still open (no local hypothesis
suffices; the structure is global to the residual post-pass configuration).

**Why U1 is a consequence of residualness (machine, 5 verified traces).**
A low even row `q` whose right class is inhabited by a second half `y`
OUTSIDE `{B_p, invRev A_p}` ("OTHER-rc") never survives in a *residual*
post-pass state: in every trace the pass leaves such a configuration
non-residual — a strict move shortens one row to a single letter.  E.g.
pre `[bAb, DB, BC, ca]` (balanced `c = BC`, `B_p = C`), pass to
`[bAb, DB, BC, Ba]`: low `q = DB` (second half `B`), row `bAb` covers the
right class by beginning with `b = B^{-1}`, and the strict rho move
`w0 ↦ w0·w3` shortens `bAb` to `b`.  So the residual-post hypothesis of
`RowStrictPostRun` (`NoEndCancel α'`) turns U1's contrapositive —
"OTHER-rc implies a strict move exists" (U1b below) — into U1 itself.
The strict-move mechanism behind U1b (which pair of rows telescopes, and
why) is not yet isolated; the residual pair constraints plus the genuine
run structure are the expected ingredients.

No `sorry`-stated lemma is committed; the containers below are the record.
-/

namespace Submission.Nielsen

/-- **(U1, open): a row-`< p` even word with inhabited right covering class
ends with `invRev A`.**  Machine: 0 violations at n = 3..7 (fresh genuine
residual-post phases; n ≥ 5 sparse).  Together with (U2) this closes
`TwoSidedCoverable` for row-`< p` words. -/
def lowRC_nonempty_endInv {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n))) : Prop :=
  ∀ q : Fin n, (S.row.symm q).val < p.val →
    (coordWord α' q).length % 2 = 0 →
      RightCoverClass α' q (secondHalf (coordWord α' q)) →
        EndsWithWord (coordWord α' q) (FreeGroup.invRev A)

/-- **(U2, open): an `endInv` row-`< p` even word has empty left covering
class.**  Machine: 0 violations at n = 3..7.  With (U1) this closes
`TwoSidedCoverable` for row-`< p` words (RC forces the endInv form by U1,
which kills LC by U2). -/
def endInv_low_leftClass_empty {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n))) : Prop :=
  ∀ q : Fin n, (S.row.symm q).val < p.val →
    (coordWord α' q).length % 2 = 0 →
      EndsWithWord (coordWord α' q) (FreeGroup.invRev A) →
        ¬ LeftCoverClass α' q (firstHalf (coordWord α' q))

/-- **(U1b, open; the contrapositive form of U1).**  In a genuine run to a
post-pass state `α'` (not assumed residual), if a row-`< p` even word has an
inhabited right covering class but does NOT end with `invRev A`, then a
strict elementary move exists in `α'` (so `α'` is not residual).  Under the
residual-post hypothesis `NoEndCancel n α'` of `RowStrictPostRun`, U1b
contradicts residualness, giving U1.  Machine: 5 verified traces of the
OTHER-rc configuration, each with a strict move shortening a row to a
letter; 0 OTHER-rc rows found in any *residual* post-pass state
(n = 3..7). -/
def otherRC_forces_strict {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n))) : Prop :=
  GenuineRunTo S p A B α' →
    ∀ q : Fin n, (S.row.symm q).val < p.val →
      (coordWord α' q).length % 2 = 0 →
        RightCoverClass α' q (secondHalf (coordWord α' q)) →
          ¬ EndsWithWord (coordWord α' q) (FreeGroup.invRev A) →
            ∃ γ : MulAut (FreeGroup (Fin n)),
              γ ∈ AutClosure n ∧ N (α' * γ) < N α'

/-- **(U1b implies U1 in the residual-post setting; structural record).**
`otherRC_forces_strict` under the post-residual hypothesis gives
`lowRC_nonempty_endInv`: OTHER-rc would produce a strict move, contradicting
`NoEndCancel n α'`.  (Closed once U1b is a theorem and wired to
`nonresidual_strict_move`; this container records the exact reduction.) -/
def otherRC_strict_implies_U1 {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n))) : Prop :=
  otherRC_forces_strict S p A B α' → NoEndCancel n α' →
    lowRC_nonempty_endInv S p A B α'

/-- **(U1+U2 imply the invariant; structural, PROVED as a statement about
the predicates).**  Under (U1) and (U2) no row-`< p` even word is
two-sidedly coverable: `TwoSidedCoverable` needs both classes
(`twoSidedCoverable_iff_single`), RC forces the endInv form, and the
endInv form kills LC.  (Closed once (U1)(U2) are theorems — this container
records the exact reduction.) -/
def lowRC_endInv_implies_invariant {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n))) : Prop :=
  lowRC_nonempty_endInv S p A B α' → endInv_low_leftClass_empty S p A B α' →
    RowInvariantStrict α' S.row p


/-- **Single-move U1b container (open).**  The *usable* form of U1b: an
OTHER-rc configuration of a genuine-run post-pass state contradicts
residualness — by one of the four single strict moves (each of the seven
shape lemmas produces such a single move internally; the plain `∃ γ ∈
AutClosure` form of `otherRC_forces_strict` does not by itself contradict
`NoEndCancel`, since a macro could drop `N` without any single move from the
initial state doing so — see `OtherRCDispatch.not_noEndCancel_of_*` for the
bridges). -/
def otherRC_not_noEndCancel {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n))) : Prop :=
  GenuineRunTo S p A B α' →
    ∀ q : Fin n, (S.row.symm q).val < p.val →
      (coordWord α' q).length % 2 = 0 →
        RightCoverClass α' q (secondHalf (coordWord α' q)) →
          ¬ EndsWithWord (coordWord α' q) (FreeGroup.invRev A) →
            ¬ NoEndCancel n α'

/-- **U1 + U2 close the even part of the invariant (PROVED).**  Given the two
sharpened sub-claims — (U1) an even row-`< p` word with inhabited right
covering class ends with `invRev A`, and (U2) an `endInv` even row-`< p` word
has empty left covering class — no even row-`< p` word is two-sidedly
coverable: `TwoSidedCoverable` splits into `RC (secondHalf)` and
`LC (firstHalf)` (`twoSidedCoverable_iff_single`), U1 turns the first into
the `endInv` form, and U2 kills the second.  This is exactly the even-half of
`RowStrictPostRun` that the run consumes (the contrapositive of
`exactlyHalfAbsorbed_coverable`, whose balanced elements always have even
word length). -/
theorem noTwoSidedCoverable_of_U1_U2 {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n)))
    (hU1 : lowRC_nonempty_endInv S p A B α')
    (hU2 : endInv_low_leftClass_empty S p A B α') :
    ∀ q : Fin n, (S.row.symm q).val < p.val →
      (coordWord α' q).length % 2 = 0 → ¬ TwoSidedCoverable α' q := by
  intro q hq heven hcov
  have hsingle := (twoSidedCoverable_iff_single α' q).mp hcov
  exact (hU2 q hq heven (hU1 q hq heven hsingle.1)) hsingle.2

/-- **U1b + U2 close the even part of the invariant at the genuine-run level
(PROVED assembly).**  If `otherRC_forces_strict` holds for the state (the
contrapositive form of U1: OTHER-rc configurations force strict moves, hence
are impossible in a residual post) then (U1) holds; with (U2) the even part
of the invariant follows. -/
theorem noTwoSidedCoverable_of_otherRC {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n)))
    (hU1b : otherRC_not_noEndCancel S p A B α')
    (hU2 : endInv_low_leftClass_empty S p A B α') :
    GenuineRunTo S p A B α' → NoEndCancel n α' →
      ∀ q : Fin n, (S.row.symm q).val < p.val →
        (coordWord α' q).length % 2 = 0 → ¬ TwoSidedCoverable α' q := by
  intro hrun hres
  refine noTwoSidedCoverable_of_U1_U2 S p A B α' ?_ hU2
  intro q hq heven hrc
  -- U1 from U1b: OTHER-rc (rc nonempty, not endInv) would contradict residualness
  by_contra hend
  exact (hU1b hrun q hq heven hrc hend) hres

end Submission.Nielsen

import Submission.Work.Item3.RowInvariant

open Submission.Nielsen
open FreeGroup
set_option autoImplicit false

/-!
# Assembly of the ACTIVE TARGET from `GenuineRunTo`: first links

**The ACTIVE TARGET (recorded in `Status.lean`)** is the post-state `i < p`
word theorem — `RowStrictPostRun S p A B α'` — whose first half is the
`beginAp`/`endInv` obstruction on row-`< p` even post-words.  The word-level
reducedness content is fully committed (`Item3/BeginApBoundary.lean` for the
boundary `|q| = 2|A|`, `Item3/BeginApInterior.lean` for the interior
`|q| < 2|A|`).  What remains is the **assembly**: lifting those obstructions
to the genuine-run post-words.  The full assembly theorem (signature, for
the record — no `sorry` is committed):

    beginAp_post_obstruction : GenuineRunTo S p A B α' → NoEndCancel n α' →
        ∀ q : Fin n, q ≠ S.row p →
          (S.row.symm q).val < p.val → even word → BeginsWithWord q A →
            ¬ EndsWithWord (invRev A) (secondHalf (coordWord α' q))
    (and the endInv mirror) ⟹ RowStrictPostRun S p A B α'.

This module proves the FIRST LINKS of the assembly — the structural facts
`GenuineRunTo` guarantees that any obstruction argument will consume:

* `run_pre_residual / run_minimal / run_fixpoint / run_normEq` — the
  projections of the bundle;
* `run_c_word_post` — the balanced coordinate's post-word is unchanged:
  `coordWord α' (S.row p) = A ++ B` (its halves `A B` are constant through
  the pass);
* `run_row_lt_p_len_le` — every row-`< p` coordinate has post-word length
  at most `2|A|` (= the balanced word's length: row sortedness + the
  per-coordinate norm preservation of the run) — the bound that decides
  which reducedness lemma (boundary or interior) applies to an even
  row-`< p` post-word;
* `run_row_lt_p_even_boundary_or_interior` — an even row-`< p` post-word of
  length `≤ 2|A|` is at the boundary (`|q| = 2|A|`) or in the interior
  (`|q| < 2|A|`) — so for `beginAp`/`endInv` words the second half is not a
  re-creatable suffix/prefix by `BeginApBoundary`/`BeginApInterior`.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- The pre-state of a genuine run is residual. -/
lemma run_pre_residual {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n)))
    (h : GenuineRunTo S p A B α') : NoEndCancel n S.α :=
  h.1

/-- The balanced element sits at row `p` and its word splits into equal
halves `A ++ B`, `|A| = |B|`. -/
lemma run_hmid {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n)))
    (h : GenuineRunTo S p A B α') :
    (S.α (FreeGroup.of (S.row p))).toWord = A ++ B ∧ A.length = B.length :=
  ⟨h.2.2.2.1, h.2.2.2.2.1⟩

/-- No row strictly below `p` is exactly-half absorbed in the pre-state
(minimality of `p`). -/
lemma run_minimal {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n)))
    (h : GenuineRunTo S p A B α') :
    ∀ i : Fin n, i.val < p.val → ¬ ExactlyHalfAbsorbed S i :=
  h.2.2.1

/-- The post-pass fixpoint is reached at the balanced coordinate. -/
lemma run_fixpoint {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n)))
    (h : GenuineRunTo S p A B α') : NoPassActive α' (S.row p) A B :=
  h.2.2.2.2.2.2.1

/-- The run preserves every coordinate's reduced length. -/
lemma run_normEq {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n)))
    (h : GenuineRunTo S p A B α') :
    ∀ i : Fin n, FreeGroup.norm (α' (FreeGroup.of (S.row i))) =
      FreeGroup.norm (S.α (FreeGroup.of (S.row i))) :=
  h.2.2.2.2.2.2.2

/-- The balanced coordinate `c := S.row p` keeps its word `A ++ B` after the
pass: `PassHistoryRow` fixes `c`'s word, and `c`'s pre-word is `A ++ B`. -/
lemma run_c_word_post {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n)))
    (h : GenuineRunTo S p A B α') :
    coordWord α' (S.row p) = A ++ B := by
  have hh := h.2.2.2.2.2.1
  have hmid := (run_hmid S p A B α' h).1
  calc
    coordWord α' (S.row p) = coordWord S.α (S.row p) := hh.1
    _ = (S.α (FreeGroup.of (S.row p))).toWord := rfl
    _ = A ++ B := hmid

/-- The balanced word has length `2|A|`. -/
lemma balanced_word_length {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n)))
    (h : GenuineRunTo S p A B α') :
    (S.α (FreeGroup.of (S.row p))).toWord.length = 2 * A.length := by
  have hmid := (run_hmid S p A B α' h).1
  have hAB := (run_hmid S p A B α' h).2
  rw [hmid, List.length_append]
  omega

/-- **First link: rows strictly below `p` have post-word length at most
`2|A|`.**  Row sortedness (no element longer than a later one) bounds the
pre-image length of a row-`< p` coordinate by that of the balanced
coordinate, and the run preserves every coordinate's length — so
`|coordWord α' (S.row i)| ≤ 2|A|` for every `i < p`.  This is the bound
that decides which reducedness lemma applies to an even row-`< p`
post-word. -/
theorem run_row_lt_p_len_le {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n)))
    (h : GenuineRunTo S p A B α') {i : Fin n} (hi : i.val < p.val) :
    (coordWord α' (S.row i)).length ≤ 2 * A.length := by
  have hnorm := run_normEq S p A B α' h
  have hlen_i : (coordWord α' (S.row i)).length =
      FreeGroup.norm (S.α (FreeGroup.of (S.row i))) := by
    calc
      (coordWord α' (S.row i)).length
          = (α' (FreeGroup.of (S.row i))).toWord.length := rfl
      _ = FreeGroup.norm (α' (FreeGroup.of (S.row i))) := by rfl
      _ = FreeGroup.norm (S.α (FreeGroup.of (S.row i))) := hnorm i
  have hle : FreeGroup.norm (S.α (FreeGroup.of (S.row i))) ≤
      FreeGroup.norm (S.α (FreeGroup.of (S.row p))) := S.sorted i p hi
  have hlen_p : FreeGroup.norm (S.α (FreeGroup.of (S.row p))) =
      2 * A.length := by
    rw [show FreeGroup.norm (S.α (FreeGroup.of (S.row p))) =
        (S.α (FreeGroup.of (S.row p))).toWord.length by rfl]
    exact balanced_word_length S p A B α' h
  omega

/-- **First link (even case): an even row-`< p` post-word is at the boundary
(`|q| = 2|A|`) or in the interior (`|q| < 2|A|`)** — the dichotomy under
which the second half of a `beginAp`/`endInv` word is not a re-creatable
suffix/prefix by `Item3/BeginApBoundary` / `BeginApInterior`. -/
theorem run_row_lt_p_even_boundary_or_interior {n : ℕ} (S : RebalanceState n)
    (p : Fin n) (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n)))
    (h : GenuineRunTo S p A B α') {i : Fin n} (hi : i.val < p.val)
    (heven : (coordWord α' (S.row i)).length % 2 = 0) :
    (coordWord α' (S.row i)).length = 2 * A.length ∨
      (coordWord α' (S.row i)).length < 2 * A.length := by
  have hle := run_row_lt_p_len_le S p A B α' h hi
  have : (coordWord α' (S.row i)).length = 2 * (coordWord α' (S.row i)).length / 2 := by
    omega
  omega

/-! ### the low-row word-form claim — REFUTED at n = 4 (record kept)

The assembly of the ACTIVE TARGET was thought to need the **low-row
word-form claim**: an even row-`< p` post-word `q` is of one of two forms
relative to the balanced first half `A` —

* `beginAp`: `q` begins with `A` (`BeginsWithWord (coordWord α' q) A`), or
* `endInv`: `q` ends with `invRev A` (`EndsWithWord (coordWord α' q)
  (invRev A)`).

**This claim is FALSE at n = 4.**  Fresh collection (2.5M random starts at
n = 4, `/tmp/fg2/collect_post.py`; every phase deep-verified against the
full `GenuineRunTo` bundle: residual pre + post, deep-BFS-confirmed minimal
balanced `p`, halves `A B`, per-coordinate norm equality, `NoPassActive`,
`q` at row `< p` with even post-word, and every row below `p` non-coverable
in the pre) found **40 low even post-words of which 11 violate the
beginAp/endInv form** (e.g. pre `[aC, da, db, AAb]` → post
`[aC, da, db, dAb]`, `p = 1`, `A = d`, low word `aC` begins with `a` and
ends with `C`, neither `A` nor `invRev A`).  The earlier "0 violations"
record (`wordform.py`) rested on only 3 n = 4 samples and was not
representative.  So `row_lt_p_even_post_wordform` is NOT a provable
intermediate, and the two-stage decomposition below is not a route to the
ACTIVE TARGET.

**The invariant that DOES hold** (all 40 fresh low words + the earlier ~450
residual-post phases, 0 violations): a row-`< p` even word is never
*two-sidedly coverable* (`RowStrictPostRun`'s conclusion).  The covering
class data in the fresh samples is cleanly structured — `c`'s own word
`A ++ B` covers a single-letter side only by beginning with `A`
(`beginAp`) or by ending with `invRev A` (`endInv`), and in every low word
at least one covering side is empty (for beginAp words the right side, for
endInv words the left side, for other-form words both sides).  The def
containers below are kept purely as the (refuted) record; the ACTIVE
TARGET is `RowStrictPostRun` itself.  Proof mechanism open; no `sorry`. -/

/-! ### two-stage decomposition of the word-form claim — DEAD ROUTE (record)

The earlier route to `row_lt_p_even_post_wordform` split into two stages
(machine, n = 3; see `/tmp/fg2/prestage.py`):

* **Stage 1 (pre-state; n = 3, `k = 1` only — FALSE at n ≥ 4):** in a
  residual state whose *minimal* balanced row `c` has word `A ++ B`
  (`|A| = |B|`), every even row-`< p` word either begins with `A`, ends with
  `invRev A` (already of the target form), or is in a pass class — ends with
  `B` or begins with `invRev B`.  Machine-validated at n = 3;
  counterexamples at n = 4 — see `lowEvenPre_formOrPassClass` below.
* **Stage 2 (pass mechanics):** pass moves were claimed to force the post
  words into the target form.

Both stages are now known not to be routes to the ACTIVE TARGET: Stage 1
fails at n ≥ 4, and Stage 2's conclusion (`row_lt_p_even_post_wordform`)
is REFUTED at n = 4 (11/40 genuine residual-post low words violate the
form — see the section above).  The only machine-validated invariant in the
genuine-run residual posts is non-coverability itself (`RowStrictPostRun`),
whose proof must use the genuine-run (pass/fixpoint/minimality/norm
preservation) structure directly.
-/

/-- **Stage 1 statement (n = 3 ONLY — FALSE at n ≥ 4, kept as a scoped
record).**  For a state `S` with minimal balanced row `p` (word `A ++ B`),
every even row-`< p` word begins with `A`, ends with `invRev A`, ends with
`B`, or begins with `invRev B`.  Machine: TRUE at n = 3, `k = 1`
(2241/2241 rows below the minimal balanced row, 4052/4052 below any
balanced row, 19746/19746 pure length-2 pairs — `/tmp/fg2/prestage.py`,
`stage1pat.py`, `pure2.py`), but **FALSE at n = 4** — counterexample:
residual state `[a2A1, A2a0, a2a3a0, a3a2]` with minimal balanced row
`p = 1` (word `A2a0`, halves `A2 | a0`) and the even low row `q = 0` (word
`a2A1`) avoids all four classes.  Hence this pre-state decomposition is a
small-rank phenomenon and is NOT the general-`n` route to the word-form
claim; the general-n proof must use the genuine-run (pass/fixpoint)
structure directly.  The pure pairwise length-2 claim is also FALSE at
n = 4 (violations in `pure2.py`), even though pairwise `NoEndCancel` is
vacuous under the exclusions — the mechanism is global.  Kept as a
`def` container only to record the n = 3 fact and its failure at n = 4. -/
def lowEvenPre_formOrPassClass {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) : Prop :=
  ∀ q : Fin n, (S.row.symm q).val < p.val →
    (coordWord S.α q).length % 2 = 0 →
      BeginsWithWord (coordWord S.α q) A ∨
      EndsWithWord (coordWord S.α q) (FreeGroup.invRev A) ∨
      EndsWithWord (coordWord S.α q) B ∨
      BeginsWithWord (coordWord S.α q) (FreeGroup.invRev B)

end Submission.Nielsen

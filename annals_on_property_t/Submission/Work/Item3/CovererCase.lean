import Submission.Work.Item3.RowForm
import Submission.Work.Item3.AssemblyRun
import Submission.Work.Item3.BranchCaseC

open Submission.Nielsen
open Commons.GroupTheory.FreeGroup
open FreeGroup
set_option autoImplicit false

/-!
# CovererCase: every coordinate of a genuine run has a last-move form; the
coverer case split of the row-`< p` invariant

The `i < p` word theorem (`RowStrictPostRun`, the ACTIVE TARGET) reads: in a
genuine run to a residual post-state `α'`, no row-`< p` even word is
two-sidedly coverable (`RowInvariantStrict`).  By
`twoSidedCoverable_iff_single` that is the conjunction
`RC (secondHalf) ∧ LC (firstHalf)`; the U1/U2 decomposition
(`UnchangedLow.lean`) splits it into

* (U1) `RC [y]` nonempty ⟹ the word ends with `invRev A` (the `endInv`
  form), and
* (U2) the `endInv` form has empty left covering class.

This module supplies the *coverer case split* that U1's proof consumes —
the reduction of "any rc-coverer forces the `endInv` form" to three explicit
impossibility configurations.  The key input is the **all-coordinate**
last-move form: in a genuine run the pass acts on every coordinate except the
balanced one (`PassHistoryState`, the current form of the `GenuineRunTo`
pass-history conjunct — strictly more faithful than the row-`< p` restriction
used before), so *every* coordinate with a changed word ends with `invRev A`
(last move an ends-move) or begins with `A` (last move a begins-move).  This
generalises `RowForm.run_moved_row_form` (which covers only rows `< p`) to all
coverers, which is what the case analysis needs.

## The classification (k = 1: `A = [a]`, `B = [b]`)

Let `q` be a row-`< p` coordinate with post-word `[x] ++ [y]`, not in the
`endInv` form (`y ≠ invRev a`), and let `u ≠ q` be an rc-coverer of `[y]`
(`u`'s word ends with `[y]` or begins with `invRev [y]`).  Then exactly one of

* **(unchanged)** `u`'s word did not change in the pass — its post-word equals
  its pre-word;
* **(ends/`invRev`)** `u`'s post-word ends with `invRev [a]` AND begins with
  `invRev [y]`;
* **(begins/`y`)** `u`'s post-word begins with `[a]` AND ends with `[y]`;

or else `y = invRev a`, i.e. `q` is in the `endInv` form (U1's conclusion).

The three non-conclusions are exactly the configurations in which the
last-move form and the covering disjunct misalign: a coverer that ends with
`invRev a` and covers by *beginning* with `invRev y`, a coverer that begins
with `a` and covers by *ending* with `y`, and a coverer that the pass did not
touch at all.  Machine record (`FallTwoRunNotes.md`): the mixed configurations
occur in *non-residual* post-states (where the run takes the strict move
instead) and never in residual ones; the reduction below makes precise that
closing U1 is exactly the impossibility of these three configurations under
`NoEndCancel α'`.

## Main declarations

* `run_history` — every coordinate `≠ S.row p` has a full pass history;
* `run_moved_form` — every coordinate with a changed word has the last-move
  form (all coordinates, not just rows `< p`);
* `coverer_case_k1` — the classification above;
* `lowRC_nonempty_endInv_of_no_bad_configs` — U1 from the impossibility of the
  three configurations.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-! ## Letter-level suffix/prefix uniqueness -/

/-- Two single-letter suffixes of the same word are equal. -/
theorem eq_of_endsWith_singleton {α : Type*} [DecidableEq α]
    {W : List (α × Bool)} {p q : α × Bool}
    (hp : EndsWithWord W [p]) (hq : EndsWithWord W [q]) : p = q := by
  rcases hp with ⟨Y, rfl⟩
  rcases hq with ⟨Z, hZ⟩
  have h : (Y ++ [p]).reverse = (Z ++ [q]).reverse := by rw [hZ]
  rw [List.reverse_append, List.reverse_append] at h
  simp only [List.reverse_singleton] at h
  exact (List.cons.inj h).1

/-- Two single-letter prefixes of the same word are equal. -/
theorem eq_of_beginsWith_singleton {α : Type*} [DecidableEq α]
    {W : List (α × Bool)} {p q : α × Bool}
    (hp : BeginsWithWord W [p]) (hq : BeginsWithWord W [q]) : p = q := by
  rcases hp with ⟨Y, hY⟩
  rcases hq with ⟨Z, hZ⟩
  have h : p :: Y = q :: Z := by
    have := hY.symm.trans hZ
    simpa using this
  exact (List.cons.inj h).1

/-- `invRev` of a single letter. -/
@[simp] theorem invRev_singleton {α : Type*} (p : α × Bool) :
    FreeGroup.invRev [p] = [(p.1, !p.2)] := by
  simp [FreeGroup.invRev]

/-- From `a = invRev y` (single letters) infer `y = invRev a`. -/
theorem eq_invRev_of_eq_invRev {α : Type*} {a y : α × Bool}
    (h : a = (y.1, !y.2)) : y = (a.1, !a.2) := by
  cases y with
  | mk y1 y2 => rw [h]; cases y2 <;> rfl

/-! ## The all-coordinate last-move form -/

/-- Every coordinate of a genuine run other than the balanced one has a full
pass history: the pass combines *every* other element of the system
(`PassHistoryState`, the pass-history conjunct of `GenuineRunTo`). -/
theorem run_history {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n)))
    (h : GenuineRunTo S p A B α') {q : Fin n} (hq : q ≠ S.row p) :
    PassWordHistory A B (coordWord S.α q) (coordWord α' q) :=
  h.2.2.2.2.2.1.2 q hq

/-- The balanced coordinate is fixed by the pass, so its word is unchanged. -/
theorem run_c_unchanged {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n)))
    (h : GenuineRunTo S p A B α') :
    coordWord α' (S.row p) = coordWord S.α (S.row p) :=
  h.2.2.2.2.2.1.1

/-- **The all-coordinate last-move form.**  In a genuine run, *any* coordinate
whose word changed during the pass ends with `invRev A` (its last move was an
ends-move) or begins with `A` (its last move was a begins-move).  This is the
all-coordinate generalisation of `RowForm.run_moved_row_form`. -/
theorem run_moved_form {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n)))
    (h : GenuineRunTo S p A B α') {q : Fin n} (hq : q ≠ S.row p)
    (hch : coordWord S.α q ≠ coordWord α' q) :
    EndsWithWord (coordWord α' q) (FreeGroup.invRev A) ∨
      BeginsWithWord (coordWord α' q) A := by
  have hhist : PassWordHistory A B (coordWord S.α q) (coordWord α' q) :=
    run_history S p A B α' h hq
  have hAB : A.length = B.length := h.2.2.2.2.1
  have hnorm := h.2.2.2.2.2.2.2 (S.row.symm q)
  have hlen : (coordWord S.α q).length = (coordWord α' q).length := by
    unfold coordWord
    have hnorm' : FreeGroup.norm (S.α (FreeGroup.of (S.row (S.row.symm q)))) =
        FreeGroup.norm (α' (FreeGroup.of (S.row (S.row.symm q)))) := hnorm.symm
    simpa [FreeGroup.norm, Equiv.apply_symm_apply] using hnorm'
  exact passWordHistory_form_of_norm_eq hhist hAB hlen hch

/-- The fixpoint reached by the pass: no coordinate other than the balanced
one ends with `B` or begins with `invRev B`, in the `WordPassFixed` form. -/
theorem run_post_fixed {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n)))
    (h : GenuineRunTo S p A B α') {q : Fin n} (hq : q ≠ S.row p) :
    WordPassFixed B (coordWord α' q) :=
  ((noPassActive_iff_all_fixed α' (S.row p) A B).mp
    (run_fixpoint S p A B α' h)) q hq

/-! ## The coverer case split at half-length 1 -/

/-- **The coverer classification (k = 1).**  In a genuine run with half-length
`1` (`A = [a]`, `B = [b]`), let `q` be a row-`< p` coordinate with post-word
`[x] ++ [y]` not in the `endInv` form (`y ≠ invRev a`), and `u ≠ q` an
rc-coverer of `[y]`.  Then `u` either

* was unchanged by the pass, or
* ends with `invRev [a]` and begins with `invRev [y]` (ends/`invRev` mixed), or
* begins with `[a]` and ends with `[y]` (begins/`y` mixed),

or `y = invRev a` — U1's conclusion.  (The coverer built out of the last-move
form and the covering disjunct can only misalign in the two mixed ways.) -/
theorem coverer_case_k1 {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (a b x y : Fin n × Bool) (α' : MulAut (FreeGroup (Fin n)))
    (h : GenuineRunTo S p [a] [b] α') {q u : Fin n}
    (hqrow : (S.row.symm q).val < p.val)
    (hqw : coordWord α' q = [x] ++ [y])
    (hNE : ¬ EndsWithWord (coordWord α' q) (FreeGroup.invRev [a]))
    (_huq : u ≠ q)
    (hcov : EndsWithWord (coordWord α' u) [y] ∨
      BeginsWithWord (coordWord α' u) (FreeGroup.invRev [y])) :
    coordWord α' u = coordWord S.α u ∨ y = (a.1, !a.2) ∨
      (EndsWithWord (coordWord α' u) (FreeGroup.invRev [a]) ∧
        BeginsWithWord (coordWord α' u) (FreeGroup.invRev [y])) ∨
      (BeginsWithWord (coordWord α' u) [a] ∧ EndsWithWord (coordWord α' u) [y]) := by
  classical
  -- `q ≠ S.row p` from the row bound.
  have hqc : q ≠ S.row p := by
    intro hqc
    rw [hqc, Equiv.symm_apply_apply] at hqrow
    exact absurd hqrow (lt_irrefl p.val)
  -- `y ≠ b` from the post-fixpoint (`NoPassActive` at `q`).
  have hfix : WordPassFixed [b] (coordWord α' q) :=
    run_post_fixed S p [a] [b] α' h hqc
  have hyb : y ≠ b := by
    intro hyb
    exact hfix.1 ⟨[x], by rw [hqw, hyb]⟩
  -- `y ≠ invRev a` is `hNE`.
  have hya : y ≠ (a.1, !a.2) := by
    intro hya
    apply hNE
    rw [hqw, invRev_singleton, hya]
    exact EndsWithWord_append [x] [(a.1, !a.2)]
  by_cases hch : coordWord S.α u = coordWord α' u
  · exact Or.inl hch.symm
  · -- `u` moved: last-move form.
    have huc : u ≠ S.row p := by
      intro huc
      exact coverer_ne_c_k1 S p a b y α' h hyb hya (by
        rw [← huc]; exact hcov)
    have hmv := run_moved_form S p [a] [b] α' h huc hch
    rcases hmv with hend | hbeg
    · rcases hcov with hcy | hcy
      · -- ends with [y] and ends with invRev [a]: two single-letter suffixes
        have hy : y = (a.1, !a.2) :=
          eq_of_endsWith_singleton hcy hend
        exact Or.inr (Or.inl hy)
      · exact Or.inr (Or.inr (Or.inl ⟨hend, hcy⟩))
    · rcases hcov with hcy | hcy
      · exact Or.inr (Or.inr (Or.inr ⟨hbeg, hcy⟩))
      · -- begins with invRev [y] and begins with [a]: two single-letter prefixes
        have hay : a = (y.1, !y.2) :=
          eq_of_beginsWith_singleton hbeg (by simpa [invRev_singleton] using hcy)
        exact Or.inr (Or.inl (eq_invRev_of_eq_invRev hay))

/-- **U1 from the three impossibility configurations (k = 1).**  If in a
genuine run at half-length `1` no rc-coverer `u` of a row-`< p` word `[x] ++ [y]`
is *unchanged*, *ends with `invRev [a]` while beginning with `invRev [y]`*, or
*begins with `[a]` while ending with `[y]`*, then the row is in the `endInv`
form — i.e. (U1) holds at `k = 1`.  Closing the three configurations is exactly
what remains of (U1). -/
theorem lowRC_nonempty_endInv_of_no_bad_configs {n : ℕ} (S : RebalanceState n)
    (p : Fin n) (a b x y : Fin n × Bool) (α' : MulAut (FreeGroup (Fin n)))
    (h : GenuineRunTo S p [a] [b] α') {q : Fin n}
    (hqrow : (S.row.symm q).val < p.val)
    (hqw : coordWord α' q = [x] ++ [y])
    (hnoUnch : ∀ u : Fin n, u ≠ q →
      (EndsWithWord (coordWord α' u) [y] ∨
        BeginsWithWord (coordWord α' u) (FreeGroup.invRev [y])) →
      coordWord S.α u ≠ coordWord α' u)
    (hnoMix1 : ∀ u : Fin n, u ≠ q →
      (EndsWithWord (coordWord α' u) [y] ∨
        BeginsWithWord (coordWord α' u) (FreeGroup.invRev [y])) →
      ¬ (EndsWithWord (coordWord α' u) (FreeGroup.invRev [a]) ∧
        BeginsWithWord (coordWord α' u) (FreeGroup.invRev [y])))
    (hnoMix2 : ∀ u : Fin n, u ≠ q →
      (EndsWithWord (coordWord α' u) [y] ∨
        BeginsWithWord (coordWord α' u) (FreeGroup.invRev [y])) →
      ¬ (BeginsWithWord (coordWord α' u) [a] ∧ EndsWithWord (coordWord α' u) [y]))
    (hcov : RightCoverClass α' q [y]) :
    EndsWithWord (coordWord α' q) (FreeGroup.invRev [a]) := by
  obtain ⟨u, huq, hcu⟩ := hcov
  by_contra hNE
  rcases coverer_case_k1 S p a b x y α' h hqrow hqw hNE huq hcu with
    hunch | hy | hmix1 | hmix2
  · exact (hnoUnch u huq hcu) hunch.symm
  · apply hNE
    have hE : EndsWithWord ([x] ++ [y]) (FreeGroup.invRev [a]) := by
      rw [invRev_singleton, ← hy]
      exact EndsWithWord_append [x] [y]
    exact hqw.symm ▸ hE
  · exact (hnoMix1 u huq hcu) hmix1
  · exact (hnoMix2 u huq hcu) hmix2

end Submission.Nielsen

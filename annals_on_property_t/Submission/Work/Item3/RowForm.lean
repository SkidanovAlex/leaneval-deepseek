import Submission.Work.Item3.RowInvariant
import Submission.Work.Item3.AssemblyRun

open Submission.Nielsen
open FreeGroup
set_option autoImplicit false

/-!
# RowForm: in a genuine run, moved row-`< p` coordinates have the last-move
form (`ends with invRev A` / `begins with A`)

Machine structure of genuine-run residual posts (`FallTwoRunNotes.md`):
combined (moved) row-`< p` words always have the last-move form — a
coordinate whose *last* pass move was an ends-move ends with `invRev A`,
one whose last move was a begins-move begins with `A` (786/786 combined
coordinates, 0 violations).  This module proves that statement from the
genuine-run hypotheses alone:

* **each pass move is length non-increasing** (`passWordMove_length_le`):
  an ends-move replaces the `B`-suffix (`|B| = |A|`) by `invRev A` and
  reduces; reduction never lengthens (`reduce_length_le`, `T3Rebalance`);
* **`GenuineRunTo` preserves per-coordinate norms**, so a moved coordinate
  has equal pre/post word lengths and every move along its history was
  exact — `red_eq_of_length_eq` (`Red.Step` removes two letters, so an
  equal-length reduction path is trivial) turns length equality into
  reducedness of the exact concatenation;
* the committed last-move form theorems
  (`passWordHistory_lastEnds_form` / `passWordHistory_lastBegins_form`).

Main theorem: `run_moved_row_form` — under `GenuineRunTo S p A B α'`, every
row-`< p` coordinate whose post-pass word differs from its pre-pass word
ends with `invRev A` or begins with `A`.  (Note this does NOT say every
row-`< p` word has the form — *unchanged* low words need not — matching the
refuted word-form claim; it is the combined-coordinate content.)

All lemmas kernel-checked; axioms `[propext, Classical.choice,
Quot.sound]`.
-/

namespace Submission.Nielsen

/-- A `Red` path with equal endpoint lengths is reflexive: every `Red.Step`
removes two letters, so a nonempty path strictly shortens. -/
theorem red_eq_of_length_eq {α : Type*} {L₁ L₂ : List (α × Bool)}
    (h : FreeGroup.Red L₁ L₂) (hlen : L₂.length = L₁.length) : L₂ = L₁ := by
  induction h with
  | refl => rfl
  | tail hb hstep ih =>
      rename_i mid fin
      exfalso
      have hle : mid.length ≤ L₁.length := FreeGroup.Red.length_le hb
      have hst := FreeGroup.Red.Step.length hstep  -- fin.length + 2 = mid.length
      have : L₁.length + 2 ≤ L₁.length := by
        calc
          L₁.length + 2 = fin.length + 2 := by rw [hlen]
          _ = mid.length := hst
          _ ≤ L₁.length := hle
      omega

/-- `|reduce L| = |L|` forces the reduction to be trivial. -/
theorem reduce_eq_of_length_eq {α : Type*} [DecidableEq α]
    (L : List (α × Bool)) (h : (FreeGroup.reduce L).length = L.length) :
    FreeGroup.reduce L = L := by
  exact red_eq_of_length_eq (FreeGroup.reduce.red (L := L)) h

/-- A word whose reduction has the same length is reduced. -/
theorem reduced_of_reduce_length_eq {α : Type*} [DecidableEq α]
    (L : List (α × Bool)) (h : (FreeGroup.reduce L).length = L.length) :
    FreeGroup.IsReduced L :=
  FreeGroup.IsReduced.of_reduce_eq (reduce_eq_of_length_eq L h)

/-- Each pass move is length non-increasing (halves of equal length). -/
theorem passWordMove_length_le {α : Type*} [DecidableEq α]
    {A B w w' : List (α × Bool)} (hAB : A.length = B.length)
    (h : PassWordMove A B w w') : w'.length ≤ w.length := by
  rcases h with ⟨Y, hw, hpost⟩ | ⟨X, hw, hpost⟩
  · -- ends-move: w = Y ++ B, w' = reduce (Y ++ invRev A)
    calc
      w'.length = (FreeGroup.reduce (Y ++ FreeGroup.invRev A)).length := by rw [hpost]
      _ ≤ (Y ++ FreeGroup.invRev A).length := reduce_length_le (Y ++ FreeGroup.invRev A)
      _ = (Y ++ B).length := by
            rw [List.length_append, List.length_append, FreeGroup.invRev_length, hAB]
      _ = w.length := by rw [hw]
  · -- begins-move: w = invRev B ++ X, w' = reduce (A ++ X)
    calc
      w'.length = (FreeGroup.reduce (A ++ X)).length := by rw [hpost]
      _ ≤ (A ++ X).length := reduce_length_le (A ++ X)
      _ = (FreeGroup.invRev B ++ X).length := by
            rw [List.length_append, List.length_append, FreeGroup.invRev_length, hAB]
      _ = w.length := by rw [hw]

/-- Histories are length non-increasing step by step. -/
theorem passWordHistory_length_le {α : Type*} [DecidableEq α]
    {A B w₀ w₁ : List (α × Bool)} (hAB : A.length = B.length)
    (h : PassWordHistory A B w₀ w₁) : w₁.length ≤ w₀.length := by
  induction h with
  | refl => rfl
  | tail hb hstep ih =>
      rename_i mid fin
      calc
        fin.length ≤ mid.length := passWordMove_length_le hAB hstep
        _ ≤ w₀.length := ih

/-- **Last-move form from equal endpoint lengths.**  A nonempty pass history
between equal-length words has an exact last move, so the final word ends
with `invRev A` (last move an ends-move) or begins with `A` (last move a
begins-move).  This is the "combined coordinates have the form" content. -/
theorem passWordHistory_form_of_norm_eq {α : Type*} [DecidableEq α]
    {A B w₀ w₁ : List (α × Bool)} (h : PassWordHistory A B w₀ w₁)
    (hAB : A.length = B.length) (hlen : w₀.length = w₁.length)
    (hne : w₀ ≠ w₁) :
    EndsWithWord w₁ (FreeGroup.invRev A) ∨ BeginsWithWord w₁ A := by
  induction h with
  | refl => exact False.elim (hne rfl)
  | tail hb hstep ih =>
      rename_i mid fin
      -- hb : PassWordHistory A B w₀ mid ; hstep : PassWordMove A B mid fin
      -- hlen : w₀.length = fin.length ; hne : w₀ ≠ fin
      have hle_mid : mid.length ≤ w₀.length := passWordHistory_length_le hAB hb
      have hle_step : fin.length ≤ mid.length := passWordMove_length_le hAB hstep
      have hmid_len : mid.length = fin.length := by omega
      rcases hstep with ⟨Y, hmid_s, hpost⟩ | ⟨X, hmid_s, hpost⟩
      · -- last move is an exact ends-move: mid = Y ++ B, fin = reduce (Y ++ invRev A)
        have hred : FreeGroup.IsReduced (Y ++ FreeGroup.invRev A) := by
          apply reduced_of_reduce_length_eq (L := Y ++ FreeGroup.invRev A)
          have hlenY : (Y ++ FreeGroup.invRev A).length = (Y ++ B).length := by
            rw [List.length_append, List.length_append, FreeGroup.invRev_length, hAB]
          calc
            (FreeGroup.reduce (Y ++ FreeGroup.invRev A)).length = fin.length := by rw [hpost]
            _ = mid.length := hmid_len.symm
            _ = (Y ++ B).length := by rw [hmid_s]
            _ = (Y ++ FreeGroup.invRev A).length := hlenY.symm
        exact Or.inl (passWordHistory_lastEnds_form A B (w := w₀) (w' := fin)
          ⟨mid, hb, Y, hmid_s, hpost, hred⟩)
      · -- last move is an exact begins-move: mid = invRev B ++ X, fin = reduce (A ++ X)
        have hred : FreeGroup.IsReduced (A ++ X) := by
          apply reduced_of_reduce_length_eq (L := A ++ X)
          have hlenX : (A ++ X).length = (FreeGroup.invRev B ++ X).length := by
            rw [List.length_append, List.length_append, FreeGroup.invRev_length, hAB]
          calc
            (FreeGroup.reduce (A ++ X)).length = fin.length := by rw [hpost]
            _ = mid.length := hmid_len.symm
            _ = (FreeGroup.invRev B ++ X).length := by rw [hmid_s]
            _ = (A ++ X).length := hlenX.symm
        exact Or.inr (passWordHistory_lastBegins_form A B (w := w₀) (w' := fin)
          ⟨mid, hb, X, hmid_s, hpost, hred⟩)

/-- **In a genuine run, moved row-`< p` coordinates have the last-move
form.**  Every row-`< p` coordinate whose post-pass word differs from its
pre-pass word ends with `invRev A` (its last move was an ends-move) or
begins with `A` (its last move was a begins-move).  Machine: 786/786
combined coordinates, 0 violations (`FallTwoRunNotes.md`). -/
theorem run_moved_row_form {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (A B : List (Fin n × Bool)) (α' : MulAut (FreeGroup (Fin n)))
    (h : GenuineRunTo S p A B α') {q : Fin n}
    (hq : (S.row.symm q).val < p.val)
    (hch : coordWord S.α q ≠ coordWord α' q) :
    EndsWithWord (coordWord α' q) (FreeGroup.invRev A) ∨
      BeginsWithWord (coordWord α' q) A := by
  have hqc : q ≠ S.row p := by
    intro hqc
    rw [hqc, Equiv.symm_apply_apply] at hq
    exact absurd hq (lt_irrefl p.val)
  have hhist : PassWordHistory A B (coordWord S.α q) (coordWord α' q) :=
    h.2.2.2.2.2.1.2 q hqc
  have hAB : A.length = B.length := h.2.2.2.2.1
  have hnorm := h.2.2.2.2.2.2.2 (S.row.symm q)
  have hlen : (coordWord S.α q).length = (coordWord α' q).length := by
    unfold coordWord
    have hnorm' : FreeGroup.norm (S.α (FreeGroup.of (S.row (S.row.symm q)))) =
        FreeGroup.norm (α' (FreeGroup.of (S.row (S.row.symm q)))) := hnorm.symm
    simpa [FreeGroup.norm, Equiv.apply_symm_apply] using hnorm'
  exact passWordHistory_form_of_norm_eq hhist hAB hlen hch

end Submission.Nielsen

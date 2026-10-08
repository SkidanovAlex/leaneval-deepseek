/-
Copyright (c) 2024. All rights reserved.

# Assembling `HigmanProp`

`Submission.Blueprint.HigmanProp` splits naturally into six statements (see `NOTES.md`):

* `center_eq_omega1`      : `Z(P) = Ω₁(P)`;
* `sq_mem_center`         : `x ^ 2 ∈ Z(P)`;
* `commutator_eq_center`  : `P' = Z(P)`;
* `card_eq_sq_or_cube`    : `|P| = q²` or `q³`;
* `type_A_classification` : the `|P| = q²` case is `A(n,θ)`;
* `type_B_C_D_classification` : the `|P| = q³` case is `B`/`C`/`D` (extension of the Prop).

This file states that decomposition as `HigmanPiecesProp` and proves
`HigmanPiecesProp → HigmanProp`.  The six statements themselves are Higman's Theorem 1
(REFS/higman_suzuki2groups.md); the ones that have been formalised so far live in the
neighbouring files.  See `NOTES.md` for the status.
-/

import Submission.Work.Higman.Class
import Submission.Work.Higman.type_B_C_D_classification
import Submission.Work.Higman.type_A_classification
import Submission.Work.Higman.center_eq_omega1_new
import Submission.Work.Higman.sq_mem_center
import Submission.Work.Higman.commutator_eq_center
import Submission.Work.Higman.card_eq_sq_or_cube

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open Classical

open LeanEval.GroupTheory.Defs

namespace Work.Higman

/-- The six statements `HigmanProp` is assembled from.  All of them are consequences of
Higman's Theorem 1; the `Nonempty (IsSuzuki2Grp P)` hypothesis is the unfolding of
`Submission.Blueprint.IsSuzukiTwoGroup P` (`Defs.lean`). -/
def HigmanPiecesProp : Prop :=
  (∀ (P : Type) [Group P] [Finite P], Nonempty (IsSuzuki2Grp P) →
      Subgroup.center P = omega1 P) ∧
  (∀ (P : Type) [Group P] [Finite P], Nonempty (IsSuzuki2Grp P) →
      ∀ x : P, x ^ 2 ∈ Subgroup.center P) ∧
  (∀ (P : Type) [Group P] [Finite P], Nonempty (IsSuzuki2Grp P) →
      commutator P = Subgroup.center P) ∧
  (∀ (P : Type) [Group P] [Finite P], Nonempty (IsSuzuki2Grp P) →
      Nat.card P = Nat.card ↥(Subgroup.center P) ^ 2 ∨
        Nat.card P = Nat.card ↥(Subgroup.center P) ^ 3) ∧
  (∀ (P : Type) [Group P] [Finite P], Nonempty (IsSuzuki2Grp P) →
      Nat.card P = Nat.card ↥(Subgroup.center P) ^ 2 →
      ∃ (n : ℕ) (e : P ≃ GaloisField 2 n × GaloisField 2 n)
        (θ : GaloisField 2 n ≃+* GaloisField 2 n),
        Nat.card ↥(Subgroup.center P) = 2 ^ n ∧ θ ≠ RingEquiv.refl _ ∧ Odd (orderOf θ) ∧
        ∀ x y : P, e (x * y) =
          ((e x).1 + (e y).1, (e x).2 + (e y).2 + (e x).1 * θ (e y).1)) ∧
  HigmanQ3Prop

/-- **The area theorem, conditional on Higman's Theorem 1.**  The `hFT` argument is kept for
interface compatibility with the other areas (this area does not use the odd order theorem). -/
theorem higmanProp_of_pieces' (h : HigmanPiecesProp) : Submission.Blueprint.HigmanProp := by
  intro P _ _ hP
  have hP' : Nonempty (IsSuzuki2Grp P) :=
    (isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp).mp hP
  have hc : Subgroup.center P = omega1 P := h.1 P hP'
  have hmem : ∀ z : P, z ∈ Subgroup.center P ↔ z ^ 2 = 1 := by
    intro z
    rw [hc]
    exact IsSuzuki2Grp.mem_omega1 hP'.some
  exact ⟨hmem, h.2.1 P hP', h.2.2.1 P hP', h.2.2.2.1 P hP', h.2.2.2.2.1 P hP'⟩

/-- **The area theorem, conditional on Higman's Theorem 1.**  The `hFT` argument is kept for
interface compatibility with the other areas (this area does not use the odd order theorem). -/
theorem higmanProp_of_pieces (hFT : Submission.Blueprint.FeitThompsonProp)
    (h : HigmanPiecesProp) : Submission.Blueprint.HigmanProp :=
  higmanProp_of_pieces' h

/-- The full extended classification from the same six statements, with no side hypothesis. -/
theorem higmanClassProp_of_pieces' (h : HigmanPiecesProp) : HigmanClassProp :=
  ⟨higmanProp_of_pieces' h, h.2.2.2.2.2⟩

/-- The full extended classification from the same six statements. -/
theorem higmanClassProp_of_pieces (hFT : Submission.Blueprint.FeitThompsonProp)
    (h : HigmanPiecesProp) : HigmanClassProp :=
  higmanClassProp_of_pieces' h

/-- **`HigmanQ3Prop` is proved** (Higman Lemma 12, via `type_B_C_D_classification`), transported
to the interface's own hypothesis `IsSuzukiTwoGroup`.  This is the statement that areas
`Hering` (App. VIII) and `PSU3` (Ch. VI §3) consume; it is axiom-clean. -/
theorem higmanQ3Prop : HigmanQ3Prop := by
  intro P _ _ hP hcard
  obtain ⟨h⟩ := (isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp).mp hP
  exact type_B_C_D_classification h hcard

/-- **The six clauses assembled**: `HigmanPiecesProp` from the area's six theorems.  This is the
only place where the six are conjoined; `higmanProp` below is then unconditional.  All six are
proved and `#print axioms` gives exactly `[propext, Classical.choice, Quot.sound]` (the last
obstruction, `NSM.deepSquareCase`, was closed on 2026-10-06 through
`Work.Higman.NSM.dsq_caseB`; see `STATUS.md`). -/
theorem higmanPiecesProp : HigmanPiecesProp :=
  ⟨fun P _ _ hP' => center_eq_omega1_new hP'.some,
   fun P _ _ hP' => sq_mem_center hP'.some,
   fun P _ _ hP' => commutator_eq_center hP'.some,
   fun P _ _ hP' => card_eq_sq_or_cube hP'.some,
   fun P _ _ hP' hcard => type_A_classification hP'.some hcard,
   higmanQ3Prop⟩

/-- **The area's deliverable**: `Submission.Blueprint.HigmanProp`, in the sharpest form — no
side hypothesis at all (the odd order theorem is not used by this area). -/
theorem higmanProp : Submission.Blueprint.HigmanProp :=
  higmanProp_of_pieces' higmanPiecesProp

/-- **The area's deliverable**, in the shape the other areas use:
`theorem X (hFT : FeitThompsonProp) : XProp`. -/
theorem higman (hFT : Submission.Blueprint.FeitThompsonProp) :
    Submission.Blueprint.HigmanProp :=
  higmanProp

/-- The full extended classification (`HigmanProp ∧ HigmanQ3Prop`), with no side hypothesis. -/
theorem higmanClass : HigmanClassProp :=
  higmanClassProp_of_pieces' higmanPiecesProp

/-- The full extended classification, in the shape the other areas use. -/
theorem higmanClassProp (hFT : Submission.Blueprint.FeitThompsonProp) : HigmanClassProp :=
  higmanClass

end Work.Higman

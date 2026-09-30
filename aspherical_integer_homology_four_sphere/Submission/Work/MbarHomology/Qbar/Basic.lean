/-
# The polytope `Q̄` as `PolytopeData`, and its face poset

**Work package W1** of `Submission/Work/NOTES_LEAD_eA.md`.

`QbarPD : PolytopeData 4` is the truncated 24-cell `Q̄` of `Work.FoldInst`, in the integral form
used by the area `ConvexCells`:

* `D = 1920`, `48` constraints: `i < 24` is the side `i` (`nrm i = sideNormal i`, `rhs i = 1`,
  so that the constraint is `0 ≤ sideSlack i y`), and `i = 24 + w` is the truncation at the ideal
  vertex `w` (`nrm i = 5 • truncNormal2 w`, `rhs i = 8`, so that the constraint is
  `0 ≤ truncSlack w y`);
* the `865` faces are rt_complex's face lattice of `Q̄`, indexed by `Fin 865`; the tight set of a
  face is the set of constraints that are equalities on it, and `pos f = 1920 · (barycentre of the
  vertices of f)`;
* `QbarCell` is the same indexing, but as a type carrying the face order
  (`f ≤ g ↔ tight g ⊆ tight f`); it is the cell type of the `PolyCW` `QbarCW`
  (`Submission/Work/MbarHomology/Qbar/CW.lean`).
-/
import Mathlib
import Submission.Work.FoldInst.Polytope
import Submission.Work.ConvexCells.Basic
import Submission.Work.MbarHomology.Data.QbarFace

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option autoImplicit false

namespace Work.MbarHomology

open Work.ConvexCells
open scoped BigOperators

noncomputable section

/-- A face of `Q̄`, indexed by rt_complex's face numbering (`Fin 865`). -/
structure QbarCell where
  /-- The rt_complex index of the face. -/
  idx : Fin 865
  deriving DecidableEq

namespace QbarCell

/-- The index of a face. -/
def equivFin : QbarCell ≃ Fin 865 where
  toFun c := c.idx
  invFun i := ⟨i⟩
  left_inv c := by cases c; rfl
  right_inv i := rfl

instance : Fintype QbarCell := Fintype.ofEquiv (Fin 865) equivFin.symm

@[ext] theorem ext {a b : QbarCell} (h : a.idx = b.idx) : a = b := by cases a; cases b; congr

end QbarCell

/-- The `48` integral normals of `Q̄`: the `24` side normals and `5 • truncNormal2`. -/
def qNrm : Fin 48 → Fin 4 → ℤ := fun i =>
  if h : (i : ℕ) < 24 then Work.FoldInst.sideNormal ⟨(i : ℕ), h⟩
  else fun j => 5 * Work.FoldInst.truncNormal2 ⟨(i : ℕ) - 24, by omega⟩ j

/-- The `48` integral right hand sides of `Q̄`. -/
def qRhs : Fin 48 → ℤ := fun i => if (i : ℕ) < 24 then 1 else 8

@[simp] theorem qNrm_castAdd (j : Fin 24) :
    qNrm (Fin.castAdd 24 j) = Work.FoldInst.sideNormal j := by
  funext k
  simp only [qNrm]
  rw [dif_pos (by simp)]
  exact congrArg (fun x : Fin 24 => Work.FoldInst.sideNormal x k) (Fin.ext rfl)

@[simp] theorem qNrm_natAdd (j : Fin 24) :
    qNrm (Fin.natAdd 24 j) = fun k => 5 * Work.FoldInst.truncNormal2 j k := by
  funext k
  simp only [qNrm]
  rw [dif_neg (by simp)]
  exact congrArg (fun x : Fin 24 => 5 * Work.FoldInst.truncNormal2 x k) (Fin.ext (by simp))

@[simp] theorem qRhs_castAdd (j : Fin 24) : qRhs (Fin.castAdd 24 j) = 1 := by
  simp only [qRhs]
  rw [if_pos (by simp)]

@[simp] theorem qRhs_natAdd (j : Fin 24) : qRhs (Fin.natAdd 24 j) = 8 := by
  simp only [qRhs]
  rw [if_neg (by simp)]

/-- The inverse code table inverts `qCode` on the tight sets of the faces of `Q̄`. -/
theorem qOfCode_qCode : ∀ f : Fin 865, qOfCode (qCode (qTight f)) = f := by decide

theorem qTight_inj {a b : Fin 865} (h : qTight a = qTight b) : a = b := by
  have h2 : qCode (qTight a) = qCode (qTight b) := congrArg qCode h
  rw [← qOfCode_qCode a, h2, qOfCode_qCode b]

instance : PartialOrder QbarCell where
  le a b := qTight b.idx ⊆ qTight a.idx
  lt a b := qTight b.idx ⊆ qTight a.idx ∧ ¬ qTight a.idx ⊆ qTight b.idx
  le_refl a := Finset.Subset.refl _
  le_trans a b c hab hbc := Finset.Subset.trans hbc hab
  le_antisymm a b hab hba :=
    QbarCell.ext (qTight_inj (Finset.Subset.antisymm hba hab))

instance : DecidableRel (· ≤ · : QbarCell → QbarCell → Prop) :=
  fun a b => inferInstanceAs (Decidable (qTight b.idx ⊆ qTight a.idx))

instance : DecidableRel (· < · : QbarCell → QbarCell → Prop) :=
  fun a b => inferInstanceAs
    (Decidable (qTight b.idx ⊆ qTight a.idx ∧ ¬ qTight a.idx ⊆ qTight b.idx))

/-- `Q̄` as a `PolytopeData`: the `48` constraints above, the `865` faces of rt_complex, and the
integral barycentres scaled by `D = 1920`. -/
def QbarPD : PolytopeData 4 where
  D := 1920
  m := 48
  K := 865
  nrm := qNrm
  rhs := qRhs
  tight := fun f => qTight f
  pos := fun f => qPos f
  top := 0
  gface := qOne
  caN := fun _ _ => 1
  caD := 1
  cbI := fun _ _ _ => 0
  bndPos := qBndPos
  bndNeg := qBndNeg
  empSel := fun _ _ => true
  empA := fun _ _ _ => 0
  empI := fun _ _ => 0
  empG := fun _ _ _ => 0
  addF := fun _ _ => (0 : Fin 865)
  addA := fun _ _ _ _ => 0
  addI := fun _ _ _ => 0
  addG := fun _ _ _ _ => 0
  addD := fun _ _ _ => 1

@[simp] theorem QbarPD_D : QbarPD.D = 1920 := rfl
@[simp] theorem QbarPD_m : QbarPD.m = 48 := rfl
@[simp] theorem QbarPD_K : QbarPD.K = 865 := rfl
@[simp] theorem QbarPD_tight (f : Fin 865) : QbarPD.tight f = qTight f := rfl
@[simp] theorem QbarPD_pos (f : Fin 865) : QbarPD.pos f = qPos f := rfl
@[simp] theorem QbarPD_nrm (i : Fin 48) : QbarPD.nrm i = qNrm i := rfl
@[simp] theorem QbarPD_rhs (i : Fin 48) : QbarPD.rhs i = qRhs i := rfl
@[simp] theorem QbarPD_top : QbarPD.top = (0 : Fin 865) := rfl

/-! ### The relation with the geometry of `Work.FoldInst` -/

/-- The `i`-th constraint of `QbarPD` in the form of an inequality of sums. -/
theorem qPD_constraint (i : Fin 48) (y : E 4) :
    inner ℝ (QbarPD.nR i) y ≤ QbarPD.bR i ↔
      ∑ j, (qNrm i j : ℝ) * y j ≤ (qRhs i : ℝ) := by
  simp only [PolytopeData.nR, PolytopeData.bR, QbarPD_D, inner_smul_left, RCLike.conj_to_real,
    inner_toE_right, inv_mul_eq_div]
  exact div_le_div_iff_of_pos_right (by norm_num)

/-- The side constraint of `Q̄` as an inequality of sums. -/
theorem side_constraint (S : Fin 24) (y : E 4) :
    (∑ j, (Work.FoldInst.sideNormal S j : ℝ) * y j ≤ 1) ↔
      0 ≤ Work.FoldInst.sideSlack S y := by
  rw [Work.FoldInst.sideSlack]
  exact Iff.symm sub_nonneg

/-- The truncation constraint of `Q̄` as an inequality of sums. -/
theorem trunc_constraint (w : Fin 24) (y : E 4) :
    (∑ j, ((5 : ℤ) * Work.FoldInst.truncNormal2 w j : ℤ) * y j ≤ (8 : ℝ)) ↔
      0 ≤ Work.FoldInst.truncSlack w y := by
  have hsum : (∑ j, (((5 : ℤ) * Work.FoldInst.truncNormal2 w j : ℤ) : ℝ) * y j)
      = 5 * ∑ j, (Work.FoldInst.truncNormal2 w j : ℝ) * y j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by push_cast; ring
  rw [Work.FoldInst.truncSlack, hsum]
  constructor
  · intro h; linarith
  · intro h; linarith

theorem QbarPD_Pset : QbarPD.Pset = Work.FoldInst.Qbar := by
  have hm : QbarPD.m = 48 := rfl
  ext y
  simp only [PolytopeData.Pset, Set.mem_setOf_eq, Work.FoldInst.Qbar, Set.mem_setOf_eq]
  constructor
  · intro h
    refine ⟨fun S => (side_constraint S y).mp ?_, fun w => (trunc_constraint w y).mp ?_⟩
    · have h1 := (qPD_constraint (Fin.castAdd 24 S) y).mp (h (Fin.castAdd 24 S))
      rwa [qNrm_castAdd, qRhs_castAdd, Int.cast_one] at h1
    · have h1 := (qPD_constraint (Fin.natAdd 24 w) y).mp (h (Fin.natAdd 24 w))
      rwa [qNrm_natAdd, qRhs_natAdd, Int.cast_ofNat] at h1
  · rintro ⟨h1, h2⟩ i
    rcases lt_or_ge (i : ℕ) 24 with hi | hi
    · have hie : i = Fin.castAdd 24 ⟨(i : ℕ), hi⟩ := Fin.ext rfl
      refine (qPD_constraint i y).mpr ?_
      rw [hie, qNrm_castAdd, qRhs_castAdd, Int.cast_one]
      exact (side_constraint ⟨(i : ℕ), hi⟩ y).mpr (h1 ⟨(i : ℕ), hi⟩)
    · have hie : i = (Fin.natAdd 24 (⟨(i : ℕ) - 24, by omega⟩ : Fin 24) : Fin 48) :=
        Fin.ext (by simp [Fin.natAdd]; omega)
      refine (qPD_constraint i y).mpr ?_
      rw [hie, qNrm_natAdd, qRhs_natAdd, Int.cast_ofNat]
      exact (trunc_constraint ⟨(i : ℕ) - 24, by omega⟩ y).mpr (h2 ⟨(i : ℕ) - 24, by omega⟩)

/-! ### The basic checks on the data

`P.OkBasic` is the decidable correctness condition of `ConvexCells`.  Its conjuncts are: the
denominator is positive; the top face has empty tight set; tight sets determine faces (proved here
through the code table `qOfCode`); the `pos` points realise the tight sets (one `decide` on
`865 × 2 × 48` integer conditions); the Farkas certificates for the faces `gface` (trivial here:
`gface i` is the facet with tight set `{i}` and all Farkas coefficients can be taken to be `1`,
`1`, `0`); and the boundedness certificate.
-/

theorem qTight_top : qTight (0 : Fin 865) = ∅ := by decide

theorem qTight_injective : ∀ f g : Fin 865, qTight f = qTight g → f = g :=
  fun _ _ h => qTight_inj h

set_option maxHeartbeats 10000000 in
theorem qPos_spec : ∀ f : Fin 865,
    (∀ i ∈ qTight f, ∑ j, qNrm i j * qPos f j = (1920 : ℤ) * qRhs i) ∧
      (∀ i, i ∉ qTight f → ∑ j, qNrm i j * qPos f j < (1920 : ℤ) * qRhs i) := by
  decide

set_option maxHeartbeats 1000000 in
theorem qFarkas_spec : (0 : ℤ) < 1 ∧ ∀ i : Fin 48,
    i ∈ qTight (qOne i) ∧ ∀ j, j ∈ qTight (qOne i) →
      (∀ k : Fin 48, 0 ≤ (0 : ℤ)) ∧
      (∀ j', 1 * qNrm i j' - ∑ k, (0 : ℤ) * qNrm k j' = 1 * qNrm j j') ∧
      (1 * qRhs j ≤ 1 * qRhs i - ∑ k, (0 : ℤ) * qRhs k) := by
  decide

set_option maxHeartbeats 1000000 in
theorem qBound_spec :
    (∀ j k, 0 ≤ qBndPos j k) ∧ (∀ j k, 0 ≤ qBndNeg j k) ∧
    (∀ j j', ∑ k, qBndPos j k * qNrm k j' = (1920 : ℤ) * (if j = j' then 1 else 0)) ∧
    (∀ j j', ∑ k, qBndNeg j k * qNrm k j' = (1920 : ℤ) * (if j = j' then -1 else 0)) := by
  decide

theorem QbarPD_okBasic : QbarPD.OkBasic :=
  ⟨by norm_num, qTight_top, qTight_injective, qPos_spec, qFarkas_spec, qBound_spec⟩

theorem QbarPD_checksBasic : QbarPD.checksBasic = true :=
  decide_eq_true_iff.mpr QbarPD_okBasic


end

end Work.MbarHomology

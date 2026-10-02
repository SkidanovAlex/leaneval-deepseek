import Mathlib
import Submission.Work.ThomBordism.Grassmann.sumPiecesSetup
import Submission.Work.ThomBordism.Grassmann.sumPiecesCont
import Submission.Work.ThomBordism.Grassmann.sumPiecesHomeo
import Submission.Work.Thom.sphereInDisc_homotopyEquiv
import Submission.Work.Thom.LineGeom

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The two pieces are homotopy equivalent to the punctured summands

The projection of the first piece `pieceFst A C` (the points whose first coordinate does not
vanish) onto the punctured total space `sumBaseA A` of the realified `A` forgets the second
coordinate, whose fibre `ℂ^b` is contractible.  This module makes that homotopy equivalence
explicit: the straight-line homotopy `(t,p) ↦ (1-t)·ι(π p) + t·p` in the fibre of the sum retracts
the piece onto the image of the section `sumFstSec`.  The same is done for the second piece.

Main results:

* `sumFstHomotopyEquiv : ↥(pieceFst A C) ≃ₕ ↥(sumBaseA A)`;
* `sumSndHomotopyEquiv : ↥(pieceSnd A C) ≃ₕ ↥(sumBaseC C)`;
* `subsingleton_Coh_pieceFst` and `subsingleton_Coh_pieceSnd`, the transfer of the vanishing of
  the cohomology of the punctured summand to the piece.
-/

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {a b : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]

/-! ## The straight-line homotopy vectors -/

/-- The straight-line combination `(1-t)·(v,0) + t·v` in the model fibre of the sum. -/
def sumHomVec (a b : ℕ) (t : ℝ) (v : EuclideanSpace ℂ (Fin (a + b))) :
    EuclideanSpace ℂ (Fin (a + b)) :=
  (1 - t) • (Work.Whitney.sumFibreC a b (fstAB a b v, 0)) + t • v

/-- The straight-line combination `(1-t)·(0,w) + t·v` in the model fibre of the sum. -/
def sumSndHomVec (a b : ℕ) (t : ℝ) (v : EuclideanSpace ℂ (Fin (a + b))) :
    EuclideanSpace ℂ (Fin (a + b)) :=
  (1 - t) • (Work.Whitney.sumFibreC a b (0, sndAB a b v)) + t • v

theorem fstAB_sumHomVec {a b : ℕ} (t : ℝ) (v : EuclideanSpace ℂ (Fin (a + b))) :
    fstAB a b (sumHomVec a b t v) = fstAB a b v := by
  show ((fstAB a b).restrictScalars ℝ) (sumHomVec a b t v) =
    ((fstAB a b).restrictScalars ℝ) v
  rw [sumHomVec, map_add, map_smul, map_smul]
  change (1 - t) • (fstAB a b (Work.Whitney.sumFibreC a b (fstAB a b v, 0))) +
      t • (fstAB a b v) = fstAB a b v
  rw [fstAB_sumFibreC, ← add_smul, sub_add_cancel, one_smul]

theorem sndAB_sumSndHomVec {a b : ℕ} (t : ℝ) (v : EuclideanSpace ℂ (Fin (a + b))) :
    sndAB a b (sumSndHomVec a b t v) = sndAB a b v := by
  show ((sndAB a b).restrictScalars ℝ) (sumSndHomVec a b t v) =
    ((sndAB a b).restrictScalars ℝ) v
  rw [sumSndHomVec, map_add, map_smul, map_smul]
  change (1 - t) • (sndAB a b (Work.Whitney.sumFibreC a b (0, sndAB a b v))) +
      t • (sndAB a b v) = sndAB a b v
  rw [sndAB_sumFibreC, ← add_smul, sub_add_cancel, one_smul]

theorem sumHomVec_zero {a b : ℕ} (v : EuclideanSpace ℂ (Fin (a + b))) :
    sumHomVec a b 0 v = Work.Whitney.sumFibreC a b (fstAB a b v, 0) := by
  simp [sumHomVec]

theorem sumHomVec_one {a b : ℕ} (v : EuclideanSpace ℂ (Fin (a + b))) :
    sumHomVec a b 1 v = v := by
  simp [sumHomVec]

theorem sumSndHomVec_zero {a b : ℕ} (v : EuclideanSpace ℂ (Fin (a + b))) :
    sumSndHomVec a b 0 v = Work.Whitney.sumFibreC a b (0, sndAB a b v) := by
  simp [sumSndHomVec]

theorem sumSndHomVec_one {a b : ℕ} (v : EuclideanSpace ℂ (Fin (a + b))) :
    sumSndHomVec a b 1 v = v := by
  simp [sumSndHomVec]

/-! ## The points of the homotopies -/

/-- The fibre coordinate of the straight-line homotopy of the first piece. -/
def sumFstHomFib
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (y : unitInterval × ↥(pieceFst A C)) : EuclideanSpace ℂ (Fin (a + b)) :=
  sumHomVec a b (y.1 : ℝ) (sumFibW A C y.2.1.1)

/-- The point of the straight-line homotopy of the first piece. -/
def sumFstHomPoint
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (y : unitInterval × ↥(pieceFst A C)) : (sumW A C).TotalSpace :=
  ⟨y.2.1.1.1, sumFstHomFib A C y⟩

/-- The fibre coordinate of the straight-line homotopy of the second piece. -/
def sumSndHomFib
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (y : unitInterval × ↥(pieceSnd A C)) : EuclideanSpace ℂ (Fin (a + b)) :=
  sumSndHomVec a b (y.1 : ℝ) (sumFibW A C y.2.1.1)

/-- The point of the straight-line homotopy of the second piece. -/
def sumSndHomPoint
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (y : unitInterval × ↥(pieceSnd A C)) : (sumW A C).TotalSpace :=
  ⟨y.2.1.1.1, sumSndHomFib A C y⟩

theorem sumFstHomFib_ne_zero
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (y : unitInterval × ↥(pieceFst A C)) : sumFstHomFib A C y ≠ 0 := by
  intro h
  have h1 : fstAB a b (sumFstHomFib A C y) = 0 := by rw [h, map_zero]
  rw [sumFstHomFib, fstAB_sumHomVec] at h1
  exact y.2.2 h1

theorem sumFstHomFib_fstAB_ne_zero
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (y : unitInterval × ↥(pieceFst A C)) : fstAB a b (sumFstHomFib A C y) ≠ 0 := by
  rw [sumFstHomFib, fstAB_sumHomVec]
  exact y.2.2

theorem sumSndHomFib_ne_zero
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (y : unitInterval × ↥(pieceSnd A C)) : sumSndHomFib A C y ≠ 0 := by
  intro h
  have h1 : sndAB a b (sumSndHomFib A C y) = 0 := by rw [h, map_zero]
  rw [sumSndHomFib, sndAB_sumSndHomVec] at h1
  exact y.2.2 h1

theorem sumSndHomFib_sndAB_ne_zero
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (y : unitInterval × ↥(pieceSnd A C)) : sndAB a b (sumSndHomFib A C y) ≠ 0 := by
  rw [sumSndHomFib, sndAB_sumSndHomVec]
  exact y.2.2

/-! ## Continuity -/

theorem continuous_sumFstHomPoint
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    Continuous (sumFstHomPoint A C) := by
  have hval : Continuous (fun y : unitInterval × ↥(pieceFst A C) => y.2.1.1) :=
    (continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd
  have hσ₁ : Continuous (fun y : unitInterval × ↥(pieceFst A C) =>
      (⟨y.2.1.1.1, sumInclC a b (sumFibA A (sumFstFn A C y.2.1.1))⟩ :
        (sumW A C).TotalSpace)) :=
    (continuous_sumIncl₁ A C).comp ((continuous_sumFstFn A C).comp hval)
  have hσ₂ : Continuous (fun y : unitInterval × ↥(pieceFst A C) =>
      (⟨y.2.1.1.1, sumFibW A C y.2.1.1⟩ : (sumW A C).TotalSpace)) :=
    hval.congr (fun y => rfl)
  have hc₁ : Continuous (fun y : unitInterval × ↥(pieceFst A C) => (1 - (y.1 : ℝ) : ℝ)) :=
    continuous_const.sub (continuous_subtype_val.comp continuous_fst)
  have hc₂ : Continuous (fun y : unitInterval × ↥(pieceFst A C) => (y.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hs₁ := Work.Thom.SphereInDisc.continuous_smul_section' (sumW A C)
    (⟨_, hσ₁⟩ : C(unitInterval × ↥(pieceFst A C), (sumW A C).TotalSpace)) ⟨_, hc₁⟩
  have hs₂ := Work.Thom.SphereInDisc.continuous_smul_section' (sumW A C)
    (⟨_, hσ₂⟩ : C(unitInterval × ↥(pieceFst A C), (sumW A C).TotalSpace)) ⟨_, hc₂⟩
  have hsum := Work.Thom.continuous_add_section (sumW A C)
    (⟨_, hs₁⟩ : C(unitInterval × ↥(pieceFst A C), (sumW A C).TotalSpace))
    (⟨_, hs₂⟩ : C(unitInterval × ↥(pieceFst A C), (sumW A C).TotalSpace)) (fun y => rfl)
  refine hsum.congr (fun y => ?_)
  rfl

theorem continuous_sumSndHomPoint
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    Continuous (sumSndHomPoint A C) := by
  have hval : Continuous (fun y : unitInterval × ↥(pieceSnd A C) => y.2.1.1) :=
    (continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd
  have hσ₁ : Continuous (fun y : unitInterval × ↥(pieceSnd A C) =>
      (⟨y.2.1.1.1, sumInclRC a b (sumFibC C (sumSndFn A C y.2.1.1))⟩ :
        (sumW A C).TotalSpace)) :=
    (continuous_sumIncl₂ A C).comp ((continuous_sumSndFn A C).comp hval)
  have hσ₂ : Continuous (fun y : unitInterval × ↥(pieceSnd A C) =>
      (⟨y.2.1.1.1, sumFibW A C y.2.1.1⟩ : (sumW A C).TotalSpace)) :=
    hval.congr (fun y => rfl)
  have hc₁ : Continuous (fun y : unitInterval × ↥(pieceSnd A C) => (1 - (y.1 : ℝ) : ℝ)) :=
    continuous_const.sub (continuous_subtype_val.comp continuous_fst)
  have hc₂ : Continuous (fun y : unitInterval × ↥(pieceSnd A C) => (y.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hs₁ := Work.Thom.SphereInDisc.continuous_smul_section' (sumW A C)
    (⟨_, hσ₁⟩ : C(unitInterval × ↥(pieceSnd A C), (sumW A C).TotalSpace)) ⟨_, hc₁⟩
  have hs₂ := Work.Thom.SphereInDisc.continuous_smul_section' (sumW A C)
    (⟨_, hσ₂⟩ : C(unitInterval × ↥(pieceSnd A C), (sumW A C).TotalSpace)) ⟨_, hc₂⟩
  have hsum := Work.Thom.continuous_add_section (sumW A C)
    (⟨_, hs₁⟩ : C(unitInterval × ↥(pieceSnd A C), (sumW A C).TotalSpace))
    (⟨_, hs₂⟩ : C(unitInterval × ↥(pieceSnd A C), (sumW A C).TotalSpace)) (fun y => rfl)
  refine hsum.congr (fun y => ?_)
  rfl

/-! ## The homotopies -/

/-- The straight-line homotopy retracting the first piece onto the image of `sumFstSec`. -/
def sumFstHomotopy
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    ContinuousMap.Homotopy (((⟨sumFstSec A C, continuous_sumFstSec A C⟩ :
        C(↥(sumBaseA A), ↥(pieceFst A C))).comp
      ⟨sumFstPiece A C, continuous_sumFstPiece A C⟩)) (ContinuousMap.id ↥(pieceFst A C)) where
  toContinuousMap :=
    ⟨fun y => ⟨⟨sumFstHomPoint A C y, sumFstHomFib_ne_zero A C y⟩,
        sumFstHomFib_fstAB_ne_zero A C y⟩,
      ((continuous_sumFstHomPoint A C).subtype_mk (fun y => sumFstHomFib_ne_zero A C y)).subtype_mk
        (fun y => sumFstHomFib_fstAB_ne_zero A C y)⟩
  map_zero_left := fun p => by
    refine Subtype.ext (Subtype.ext ?_)
    show (⟨p.1.1.1, sumHomVec a b 0 (sumFibW A C p.1.1)⟩ : (sumW A C).TotalSpace) =
      (⟨p.1.1.1, Work.Whitney.sumFibreC a b (fstAB a b (sumFibW A C p.1.1), 0)⟩ :
        (sumW A C).TotalSpace)
    rw [sumHomVec_zero]
  map_one_left := fun p => by
    refine Subtype.ext (Subtype.ext ?_)
    show (⟨p.1.1.1, sumHomVec a b 1 (sumFibW A C p.1.1)⟩ : (sumW A C).TotalSpace) = p.1.1
    rw [sumHomVec_one]
    rfl

/-- The straight-line homotopy retracting the second piece onto the image of `sumSndSec`. -/
def sumSndHomotopy
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    ContinuousMap.Homotopy (((⟨sumSndSec A C, continuous_sumSndSec A C⟩ :
        C(↥(sumBaseC C), ↥(pieceSnd A C))).comp
      ⟨sumSndPiece A C, continuous_sumSndPiece A C⟩)) (ContinuousMap.id ↥(pieceSnd A C)) where
  toContinuousMap :=
    ⟨fun y => ⟨⟨sumSndHomPoint A C y, sumSndHomFib_ne_zero A C y⟩,
        sumSndHomFib_sndAB_ne_zero A C y⟩,
      ((continuous_sumSndHomPoint A C).subtype_mk (fun y => sumSndHomFib_ne_zero A C y)).subtype_mk
        (fun y => sumSndHomFib_sndAB_ne_zero A C y)⟩
  map_zero_left := fun p => by
    refine Subtype.ext (Subtype.ext ?_)
    show (⟨p.1.1.1, sumSndHomVec a b 0 (sumFibW A C p.1.1)⟩ : (sumW A C).TotalSpace) =
      (⟨p.1.1.1, Work.Whitney.sumFibreC a b (0, sndAB a b (sumFibW A C p.1.1))⟩ :
        (sumW A C).TotalSpace)
    rw [sumSndHomVec_zero]
  map_one_left := fun p => by
    refine Subtype.ext (Subtype.ext ?_)
    show (⟨p.1.1.1, sumSndHomVec a b 1 (sumFibW A C p.1.1)⟩ : (sumW A C).TotalSpace) = p.1.1
    rw [sumSndHomVec_one]
    rfl

/-! ## The homotopy equivalences and the transfers of vanishing -/

/-- **The first piece is homotopy equivalent to the punctured total space of `A`.** -/
noncomputable def sumFstHomotopyEquiv
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    ContinuousMap.HomotopyEquiv ↥(pieceFst A C) ↥(sumBaseA A) where
  toFun := ⟨sumFstPiece A C, continuous_sumFstPiece A C⟩
  invFun := ⟨sumFstSec A C, continuous_sumFstSec A C⟩
  left_inv := ⟨sumFstHomotopy A C⟩
  right_inv := by
    rw [show ((⟨sumFstPiece A C, continuous_sumFstPiece A C⟩ :
        C(↥(pieceFst A C), ↥(sumBaseA A))).comp
        ⟨sumFstSec A C, continuous_sumFstSec A C⟩) = ContinuousMap.id _ from
      ContinuousMap.ext (fun q => sumFstPiece_sumFstSec A C q)]

/-- **The second piece is homotopy equivalent to the punctured total space of `C`.** -/
noncomputable def sumSndHomotopyEquiv
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    ContinuousMap.HomotopyEquiv ↥(pieceSnd A C) ↥(sumBaseC C) where
  toFun := ⟨sumSndPiece A C, continuous_sumSndPiece A C⟩
  invFun := ⟨sumSndSec A C, continuous_sumSndSec A C⟩
  left_inv := ⟨sumSndHomotopy A C⟩
  right_inv := by
    rw [show ((⟨sumSndPiece A C, continuous_sumSndPiece A C⟩ :
        C(↥(pieceSnd A C), ↥(sumBaseC C))).comp
        ⟨sumSndSec A C, continuous_sumSndSec A C⟩) = ContinuousMap.id _ from
      ContinuousMap.ext (fun q => sumSndPiece_sumSndSec A C q)]

/-- The vanishing of the cohomology of the punctured total space of `A` transfers to the first
piece. -/
theorem subsingleton_Coh_pieceFst
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) (m : ℕ)
    (h : Subsingleton (Work.Thom.Coh ℤ m ↥(sumBaseA A))) :
    Subsingleton (Work.Thom.Coh ℤ m ↥(pieceFst A C)) := by
  have hbij := Work.Thom.bijective_CohMap_of_homotopyEquiv (sumFstHomotopyEquiv A C) ℤ m
  exact ⟨fun x y => by
    obtain ⟨x', rfl⟩ := hbij.2 x
    obtain ⟨y', rfl⟩ := hbij.2 y
    rw [h.elim x' y']⟩

/-- The vanishing of the cohomology of the punctured total space of `C` transfers to the second
piece. -/
theorem subsingleton_Coh_pieceSnd
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) (m : ℕ)
    (h : Subsingleton (Work.Thom.Coh ℤ m ↥(sumBaseC C))) :
    Subsingleton (Work.Thom.Coh ℤ m ↥(pieceSnd A C)) := by
  have hbij := Work.Thom.bijective_CohMap_of_homotopyEquiv (sumSndHomotopyEquiv A C) ℤ m
  exact ⟨fun x y => by
    obtain ⟨x', rfl⟩ := hbij.2 x
    obtain ⟨y', rfl⟩ := hbij.2 y
    rw [h.elim x' y']⟩

end

end Work.ThomBordism.Grassmann

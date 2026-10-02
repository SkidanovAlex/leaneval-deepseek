import Mathlib
import Submission.Work.ThomBordism.Grassmann.sumPiecesSetup
import Submission.Work.ThomBordism.Grassmann.sumPiecesCont
import Submission.Work.ThomBordism.Grassmann.isOpen_pieceFst_pieceSnd
import Submission.Work.LerayHirsch.nonempty_homeo_projSpace_bundleComap_subtype

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The pieces of the zero complement of a Whitney sum: the homeomorphisms

For complex bundles `A` (rank `a`) and `C` (rank `b`) over `B`, this module proves that the pieces
of the cover of `zeroComplement (sumW A C)` are the total spaces of the punctured summands and of
the pullback of the second summand to the punctured first summand:

* `sumFstPiece`/`sumFstSec` are continuous and mutually inverse (`sumFstPiece_sumFstSec`);
* `sumSndPiece`/`sumSndSec` are continuous and mutually inverse;
* `sumPHomeo : ↥(sumP A C) ≃ₜ ↥(pieceFst A C ∩ pieceSnd A C)` identifies the piece of the pullback
  `zeroComplement (sumZ1 A C)` over `sumBaseA` with the intersection of the two pieces;
* `sumUVHomeo : ↥(zeroComplement (sumZ A C)) ≃ₜ ↥(pieceFst A C ∩ pieceSnd A C)` is the composite
  of `sumPHomeo` with `Work.LerayHirsch.punctHomeo`.
-/

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {a b : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]

/-! ## Continuity of the projection/inclusion of the pieces -/

theorem continuous_sumFstPiece
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    Continuous (sumFstPiece A C) :=
  ((continuous_sumFstFn A C).comp
    (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk (fun p => p.2)

theorem continuous_sumSndPiece
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    Continuous (sumSndPiece A C) :=
  ((continuous_sumSndFn A C).comp
    (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk (fun p => p.2)

theorem continuous_sumFstSec
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    Continuous (sumFstSec A C) :=
  (((continuous_sumIncl₁ A C).comp continuous_subtype_val).subtype_mk (fun q => by
      show Work.Whitney.sumFibreC a b (sumFibPA A q, 0) ≠ 0
      intro h
      exact sumFibPA_ne_zero A q ((sumFibreC_eq_zero_iff a b).mp h).1)).subtype_mk (fun q => by
    show fstAB a b (Work.Whitney.sumFibreC a b (sumFibPA A q, 0)) ≠ 0
    rw [fstAB_sumFibreC]
    exact sumFibPA_ne_zero A q)

theorem continuous_sumSndSec
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    Continuous (sumSndSec A C) :=
  (((continuous_sumIncl₂ A C).comp continuous_subtype_val).subtype_mk (fun q => by
      show Work.Whitney.sumFibreC a b (0, sumFibPC C q) ≠ 0
      intro h
      exact sumFibPC_ne_zero C q ((sumFibreC_eq_zero_iff a b).mp h).2)).subtype_mk (fun q => by
    show sndAB a b (Work.Whitney.sumFibreC a b (0, sumFibPC C q)) ≠ 0
    rw [sndAB_sumFibreC]
    exact sumFibPC_ne_zero C q)

/-- The real-flavoured continuity of `sumPhi` (on the realified total space of the pullback). -/
theorem continuous_sumPhi_real
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    Continuous (fun p : (sumZ1 A C).TotalSpace =>
      (⟨p.1.1, Work.Whitney.sumFibreC a b (sumFibA A p.1, sumFibZ1 A C p)⟩ :
        (sumW A C).TotalSpace)) :=
  (continuous_sumPhi A C).comp (Work.Thom.continuous_id_realification_symm (sumZ1c A C))

/-- The identity from the total space of the pullback `sumZ1c A C` (complex topology) to the
total space of its realification `sumZ1 A C`. -/
def sumZId (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (x : (sumZ1c A C).TotalSpace) : (sumZ1 A C).TotalSpace := x

theorem continuous_sumZId
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    Continuous (sumZId A C) :=
  Work.Thom.continuous_id_realification (sumZ1c A C)

theorem sumFibZ1_sumZId
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (x : (sumZ1c A C).TotalSpace) : sumFibZ1 A C (sumZId A C x) = sumFibZ1 A C x := rfl

theorem sumProj_sumZId
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (x : (sumZ1c A C).TotalSpace) : (sumZId A C x).proj = x.proj := rfl

/-! ## The coordinates of `sumPhi` and `sumPsi` -/

theorem sumFibW_sumPhi
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) (z : ↥(sumP A C)) :
    sumFibW A C (sumPhi A C z.1.1) =
      Work.Whitney.sumFibreC a b (sumFibA A z.1.1.1, sumFibZ1 A C z.1.1) := by
  rw [sumPhi_apply, sumFibW_mk]

theorem sumFstAB_sumPhi
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) (z : ↥(sumP A C)) :
    fstAB a b (sumFibW A C (sumPhi A C z.1.1)) = sumFibA A z.1.1.1 := by
  rw [sumFibW_sumPhi, fstAB_sumFibreC]

theorem sumSndAB_sumPhi
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) (z : ↥(sumP A C)) :
    sndAB a b (sumFibW A C (sumPhi A C z.1.1)) = sumFibZ1 A C z.1.1 := by
  rw [sumFibW_sumPhi, sndAB_sumFibreC]

theorem sumFibW_sumPhi_ne_zero
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) (z : ↥(sumP A C)) :
    sumFibW A C (sumPhi A C z.1.1) ≠ 0 := by
  intro h
  have h1 := sumFstAB_sumPhi A C z
  rw [h, map_zero] at h1
  exact z.2 h1.symm

theorem sumFstAB_sumPhi_ne_zero
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) (z : ↥(sumP A C)) :
    fstAB a b (sumFibW A C (sumPhi A C z.1.1)) ≠ 0 := by
  rw [sumFstAB_sumPhi]
  exact z.2

theorem sumSndAB_sumPhi_ne_zero
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) (z : ↥(sumP A C)) :
    sndAB a b (sumFibW A C (sumPhi A C z.1.1)) ≠ 0 := by
  rw [sumSndAB_sumPhi]
  exact z.1.2

theorem sumFibZ1_sumPsi
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (p : (sumW A C).TotalSpace) :
    sumFibZ1 A C (sumPsi A C p) = sndAB a b (sumFibW A C p) := by
  rw [sumPsi_apply, sumFibZ1]

theorem sumFibA_sumPsi
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (p : (sumW A C).TotalSpace) :
    sumFibA A (sumPsi A C p).1 = fstAB a b (sumFibW A C p) := by
  rw [sumPsi_apply, sumFibA]

/-! ## The identification `sumP ≃ pieceFst ∩ pieceSnd` -/

/-- The identification of the piece of the pullback with the intersection of the two pieces. -/
def sumPToUV (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    ↥(sumP A C) → ↥(pieceFst A C ∩ pieceSnd A C) :=
  fun z => ⟨⟨sumPhi A C z.1.1, sumFibW_sumPhi_ne_zero A C z⟩,
    Set.mem_inter (sumFstAB_sumPhi_ne_zero A C z) (sumSndAB_sumPhi_ne_zero A C z)⟩

/-- The inverse identification. -/
def sumUVToP (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    ↥(pieceFst A C ∩ pieceSnd A C) → ↥(sumP A C) :=
  fun z => ⟨⟨sumZId A C (sumPsi A C z.1.1), by
      show sumFibZ1 A C (sumZId A C (sumPsi A C z.1.1)) ≠ 0
      rw [sumFibZ1_sumZId, sumFibZ1_sumPsi]
      exact z.2.2⟩, by
      show (sumZId A C (sumPsi A C z.1.1)).proj ∈ sumBaseA A
      rw [sumProj_sumZId]
      show sumFibA A (sumPsi A C z.1.1).1 ≠ 0
      rw [sumFibA_sumPsi]
      exact z.2.1⟩

theorem continuous_sumPToUV
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    Continuous (sumPToUV A C) := by
  have h1 : Continuous (fun z : ↥(sumP A C) => sumPhi A C z.1.1) :=
    (continuous_sumPhi_real A C).comp (continuous_subtype_val.comp continuous_subtype_val)
  have h2 : Continuous (fun z : ↥(sumP A C) =>
      (⟨sumPhi A C z.1.1, sumFibW_sumPhi_ne_zero A C z⟩ :
        ↥(Work.Thom.zeroComplement (sumW A C)))) :=
    h1.subtype_mk (fun z => sumFibW_sumPhi_ne_zero A C z)
  exact h2.subtype_mk (fun z =>
    Set.mem_inter (sumFstAB_sumPhi_ne_zero A C z) (sumSndAB_sumPhi_ne_zero A C z))

theorem continuous_sumUVToP
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    Continuous (sumUVToP A C) := by
  have h1 : Continuous (fun z : ↥(pieceFst A C ∩ pieceSnd A C) =>
      sumZId A C (sumPsi A C z.1.1)) :=
    (continuous_sumZId A C).comp ((continuous_sumPsi A C).comp
      (continuous_subtype_val.comp continuous_subtype_val))
  have h2 : Continuous (fun z : ↥(pieceFst A C ∩ pieceSnd A C) =>
      (⟨sumZId A C (sumPsi A C z.1.1), by
        show sumFibZ1 A C (sumZId A C (sumPsi A C z.1.1)) ≠ 0
        rw [sumFibZ1_sumZId, sumFibZ1_sumPsi]
        exact z.2.2⟩ : ↥(Work.Thom.zeroComplement (sumZ1 A C)))) :=
    h1.subtype_mk (fun z => by
      show sumFibZ1 A C (sumZId A C (sumPsi A C z.1.1)) ≠ 0
      rw [sumFibZ1_sumZId, sumFibZ1_sumPsi]
      exact z.2.2)
  exact h2.subtype_mk (fun z => by
    show (⟨sumZId A C (sumPsi A C z.1.1), by
        show sumFibZ1 A C (sumZId A C (sumPsi A C z.1.1)) ≠ 0
        rw [sumFibZ1_sumZId, sumFibZ1_sumPsi]
        exact z.2.2⟩ : ↥(Work.Thom.zeroComplement (sumZ1 A C))).1.proj ∈ sumBaseA A
    rw [sumProj_sumZId]
    show sumFibA A (sumPsi A C z.1.1).1 ≠ 0
    rw [sumFibA_sumPsi]
    exact z.2.1)

theorem sumUVToP_sumPToUV
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (z : ↥(sumP A C)) : sumUVToP A C (sumPToUV A C z) = z := by
  refine Subtype.ext (Subtype.ext ?_)
  show sumZId A C (sumPsi A C (sumPhi A C z.1.1)) = z.1.1
  rw [sumPsi_sumPhi]
  rfl

theorem sumPToUV_sumUVToP
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (z : ↥(pieceFst A C ∩ pieceSnd A C)) : sumPToUV A C (sumUVToP A C z) = z := by
  refine Subtype.ext (Subtype.ext ?_)
  show sumPhi A C (sumPsi A C z.1.1) = z.1.1
  rw [sumPhi_sumPsi]

/-- **The piece of the pullback is homeomorphic to the intersection of the two pieces.** -/
noncomputable def sumPHomeo
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    ↥(sumP A C) ≃ₜ ↥(pieceFst A C ∩ pieceSnd A C) where
  toFun := sumPToUV A C
  invFun := sumUVToP A C
  left_inv := sumUVToP_sumPToUV A C
  right_inv := sumPToUV_sumUVToP A C
  continuous_toFun := continuous_sumPToUV A C
  continuous_invFun := continuous_sumUVToP A C

/-- **The zero complement of the pullback `sumZ A C` is homeomorphic to the intersection of the
two pieces.** -/
noncomputable def sumUVHomeo
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    ↥(Work.Thom.zeroComplement (sumZ A C)) ≃ₜ ↥(pieceFst A C ∩ pieceSnd A C) :=
  (Work.LerayHirsch.punctHomeo (sumZ1c A C) (sumBaseA A)).trans (sumPHomeo A C)

end

end Work.ThomBordism.Grassmann

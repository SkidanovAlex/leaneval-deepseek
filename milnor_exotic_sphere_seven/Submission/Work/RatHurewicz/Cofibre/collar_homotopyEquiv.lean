import Mathlib
import Submission.Work.RatHurewicz.Cofibre.StableRangeDefs
import Submission.Work.RatHurewicz.Cofibre.Maps
import Submission.Work.RatHurewicz.Cofibre.URetractEqv
import Submission.Work.RatHurewicz.Cofibre.coneMidHomotopyEquiv
import Submission.Work.RatHurewicz.Cofibre.collarHomotopyEquiv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.RatHurewicz.Cofibre

/-- **The collar `U ∩ V` is homotopy equivalent to `F`, with the "base of a cone point" as the
forward map and the "raise" `collarRaise` as its homotopy inverse.**

`U ∩ V = cofibreU ι ∩ cofibreV ι` is the set of cone points of height in `(0, 1/2)`
(`mem_cofibreU_inter_cofibreV_iff`); the map `b : U ∩ V → F`, `[y,t] ↦ y`, is continuous (it
descends through the quotient: on the half-open cone `coneLtHalfSet` the fibre of `coneMk` is a
singleton, exactly the argument of `coneBaseFun_factors`, but with codomain `F`), and
`b ∘ collarRaise = id` while `collarRaise ∘ b = id` up to the cone-line homotopy
`[y,t] ↦ [y, (1-s)t + s/4]` (which stays in `(0,1/2)`).

The existing `collarMidHomotopyEquiv`/`coneMidHomotopyEquiv` already provide such an equivalence
(forward map `coneMidProj ∘ collarToMid`, inverse `midToCollar ∘ coneMidSec`, and
`coneMidSec x = [x, 1/4]`), so both conjuncts hold for those; the only extra work is the `F = ∅`
case split (`Cone ∅ = ∅`, hence the collar is empty and both conjuncts are vacuous).

This is the second component of the map of pairs `(U, U∩V) → (E, range ι)` used for the excision
comparison `C_*(E, F) ≅ C_*(cofibre ι, V)`; `Work.Cohomology.homologyEquiv` turns the homotopy
equivalence into `IsIso` of the induced chain maps. -/
theorem collar_homotopyEquiv {E F : Type} [TopologicalSpace E] [TopologicalSpace F]
    (ι : C(F, E)) :
    ∃ (f : ContinuousMap.HomotopyEquiv ↥(Work.RatHurewicz.cofibreU ι ∩
        Work.RatHurewicz.cofibreV ι) F),
      (∀ y : F, f.toFun (Work.RatHurewicz.collarPt ι y) = y) ∧
      (∀ y : F, f.invFun y = Work.RatHurewicz.collarPt ι y) := by
  have hstub : collarStub = coneQuarter := Subtype.ext rfl
  by_cases hF : Nonempty F
  · haveI : Nonempty F := hF
    have hcomp : (coneMidProj (F := F)).comp (coneMidSec (F := F)) = ContinuousMap.id F := by
      ext x
      show coneMidProj (F := F) (coneMidMk (F := F) ⟨(x, coneQuarter), coneMid_mem_sec (F := F) x⟩) = x
      exact coneMidProj_coneMidMk (F := F) ⟨(x, coneQuarter), coneMid_mem_sec (F := F) x⟩
    have hproj : ∀ y : F, coneMidProj (F := F) (coneMidSec (F := F) y) = y := by
      intro y
      simpa using congrFun (congrArg (fun k : C(F, F) => ⇑k) hcomp) y
    let cm : ContinuousMap.HomotopyEquiv ↥(midSet (F := F)) F :=
      { toFun := coneMidProj (F := F)
        invFun := coneMidSec (F := F)
        left_inv := ⟨(coneMidHomotopyId (F := F)).symm⟩
        right_inv := by rw [hcomp] }
    refine ⟨(collarMidHomotopyEquiv ι).trans cm, ?_, ?_⟩
    · intro y
      rw [ContinuousMap.HomotopyEquiv.trans_apply]
      have hmemMid : coneMk (F := F) (y, collarStub) ∈ midSet (F := F) := by
        show (0 : unitInterval) < coneHeight (coneMk (F := F) (y, collarStub)) ∧
          coneHeight (coneMk (F := F) (y, collarStub)) < cofibreHalf
        rw [coneHeight_coneMk]
        exact ⟨collarStub_pos, collarStub_lt_half⟩
      have hmem : (Sum.inr (coneMk (F := F) (y, collarStub)) : E ⊕ Work.Stems.Cone F) ∈
          (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' (cofibreU ι ∩ cofibreV ι) := by
        rw [preimage_collar ι]
        exact ⟨coneMk (F := F) (y, collarStub), hmemMid, rfl⟩
      have hpt : collarPt ι y =
          (⟨Quotient.mk'' (Sum.inr (coneMk (F := F) (y, collarStub))), hmem⟩ :
            ↥(cofibreU ι ∩ cofibreV ι)) := Subtype.ext rfl
      have hmid : collarToMid ι (collarPt ι y) = coneMidSec (F := F) y := by
        rw [hpt, collarToMid_mk ι (Sum.inr (coneMk (F := F) (y, collarStub))) hmem,
          collarToMidRaw_inr ι hmem rfl hmemMid]
        apply Subtype.ext
        show coneMk (F := F) (y, collarStub) = coneMk (F := F) (y, coneQuarter)
        rw [hstub]
      show coneMidProj (F := F) (collarToMid ι (collarPt ι y)) = y
      rw [hmid]
      exact hproj y
    · intro y
      show midToCollar ι (coneMidSec (F := F) y) = collarPt ι y
      apply Subtype.ext
      show cofibreInclCone ι (coneMk (F := F) (y, coneQuarter)) =
        cofibreInclCone ι (coneMk (F := F) (y, collarStub))
      rw [hstub]
  · haveI hFempty : IsEmpty F := not_nonempty_iff.mp hF
    haveI hCone : IsEmpty (Work.Stems.Cone F) := ⟨fun q => by
      obtain ⟨a, -⟩ := Quotient.mk''_surjective (s₁ := Work.Stems.coneSetoid F) q
      exact isEmptyElim a.1⟩
    have hmidEmpty : midSet (F := F) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      exact isEmptyElim y
    have hpre : (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹'
        (cofibreU ι ∩ cofibreV ι) = ∅ := by
      rw [preimage_collar ι, hmidEmpty, Set.image_empty]
    haveI hcollar : IsEmpty ↥(cofibreU ι ∩ cofibreV ι) := ⟨fun z => by
      obtain ⟨a, ha⟩ := Quotient.mk''_surjective (s₁ := Relation.EqvGen.setoid (cofibreRel ι)) z.1
      have h : a ∈ (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹'
          (cofibreU ι ∩ cofibreV ι) := by
        show (Quotient.mk'' a : cofibre ι) ∈ cofibreU ι ∩ cofibreV ι
        rw [ha]; exact z.2
      rw [hpre] at h
      exact h⟩
    let Φ : C(↥(cofibreU ι ∩ cofibreV ι), F) :=
      ⟨fun x => isEmptyElim x, continuous_iff_continuousAt.mpr (fun x => isEmptyElim x)⟩
    let Ψ : C(F, ↥(cofibreU ι ∩ cofibreV ι)) :=
      ⟨fun y => isEmptyElim y, continuous_iff_continuousAt.mpr (fun y => isEmptyElim y)⟩
    refine ⟨{ toFun := Φ, invFun := Ψ, left_inv := ?_, right_inv := ?_ }, ?_, ?_⟩
    · have h : Ψ.comp Φ = ContinuousMap.id _ := Subsingleton.elim _ _
      rw [h]
    · have h : Φ.comp Ψ = ContinuousMap.id _ := Subsingleton.elim _ _
      rw [h]
    · intro y; exact isEmptyElim y
    · intro y; exact isEmptyElim y


end Work.RatHurewicz.Cofibre

import Mathlib
import Submission.Work.Whitney.tcmRelCup_unit_right
import Submission.Work.Whitney.tcmUnitLeft

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The left unit law of the canonical relative–relative cup, low degree

`Work.Whitney.tcmRelCup_unit_left_one` is the left unit law `(relCohMap id C (A∪C)).hom
(tcmRelCup A C hA hC 0 n u b) = b` (with `u` a degree-`0` class whose absolute image is the unit)
in the *smallest* degree configuration `n = 1`.

The general statement is reviewed and parked under the path `Whitney/tcmRelCup_unit_left`; the
degree-`1` instance proved here is the one that the `n = 0` case of the ranked-one signed model
product formula consumes, and it is the instance in which the degree bookkeeping of the mirror of
`Work.Whitney.tcmRelCup_unit_right` is *cast-free* (`0 + 1` is definitionally `1`, whereas the
general `0 + n` is not definitionally `n`; cf. the warning in `tcmUnitLeft.lean`).

The proof is the mirror of the proved right unit law with `pdABProjC` (the projection of the
`A+C` complex onto the `C`-complex, from `tcmUnitLeft.lean`) in place of `pdABProj`, the identity
`pdABInclRelR_comp_pdABProjC` in place of `pdABInclRelR_comp_pdABProj`/`relComplexMap_id_coe`,
`Or.inr` in place of `Or.inl`, and the *first* conjunct of `Work.Cohomology.cupUnit` in place of the
second.
-/

namespace Work.Whitney

open Work.Thom
open Work.Cohomology
open CategoryTheory

noncomputable section

/-- **The left unit law of the canonical relative–relative cup at degree `(0,1)`**: for an open
`A, C ⊆ X` and a class `u ∈ H^0(X,A)` with absolute image the unit class, cupping a class
`a ∈ H^1(X,C)` with `u` on the left and forgetting the `A`-relative data returns `a`. -/
theorem tcmRelCup_unit_left_one {X : Type} [TopologicalSpace X] (A C : Set X) (hA : IsOpen A)
    (hC : IsOpen C) (u : RelCoh ℤ 0 X A) (a : RelCoh ℤ 1 X C)
    (hu : (Work.Thom.relToAbs ℤ A 0).hom u
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of X))) :
    (Work.Thom.relCohMap (ContinuousMap.id X) C (A ∪ C) (fun x hx => Or.inr hx) ℤ 1).hom
      (Work.Whitney.tcmRelCup A C hA hC 0 1 u a) = a := by
  obtain ⟨α, hα, rfl⟩ := exists_relClassOf ℤ (TopCat.of X) A 0 u
  obtain ⟨β, hβ, rfl⟩ := exists_relClassOf ℤ (TopCat.of X) C 1 a
  have hαunit : α.1 = Work.Cohomology.unitCochain ℤ (TopCat.toSSet.obj (TopCat.of X)) :=
    relClassOf_relToAbs_oneH_coe A α hα hu
  have hα' : ((relComplex ℤ (TopCat.of X) A).d 0 (0 + 1)).hom α = 0 := by
    rw [relComplex_d_apply]; exact hα
  have hβ' : ((relComplex ℤ (TopCat.of X) C).d 1 (1 + 1)).hom β = 0 := by
    rw [relComplex_d_apply]; exact hβ
  have hstar : ((pdABCohR (R := ℤ) (TopCat.of X) A C).d (0 + 1) (0 + 1 + 1)).hom
      (((starAB (TopCat.of X) A C 0 1) α) β) = 0 :=
    ThreeCup.star3_cocycle_cochain (Leibniz3_starAB (TopCat.of X) A C) 0 1 α β hα' hβ'
  set γ : (pdABCohR (R := ℤ) (TopCat.of X) A C).X (0 + 1) :=
    (((starAB (TopCat.of X) A C 0 1) α) β) with hγdef
  have hγ : ((pdABCohR (R := ℤ) (TopCat.of X) A C).d (0 + 1) (0 + 1 + 1)).hom γ = 0 := hstar
  have hcoe : cocycleOfK (pdABCohR (R := ℤ) (TopCat.of X) A C) γ hγ
      = cocycleOfK (pdABCohR (R := ℤ) (TopCat.of X) A C)
          (((starAB (TopCat.of X) A C 0 1) α) β) hstar := by
    apply iCycles_injective_K (pdABCohR (R := ℤ) (TopCat.of X) A C) (0 + 1)
    rw [iCycles_cocycleOfK]
  have hY : relRelCupHMap (R := ℤ) (TopCat.of X) A C 0 1
        (relClassOf ℤ (TopCat.of X) A α hα) (relClassOf ℤ (TopCat.of X) C β hβ)
      = (HomologicalComplex.homologyπ (pdABCohR (R := ℤ) (TopCat.of X) A C) (0 + 1)).hom
          (cocycleOfK (pdABCohR (R := ℤ) (TopCat.of X) A C) γ hγ) := by
    rw [relClassOf_eq_homologyπ_cocycleOfK ℤ (TopCat.of X) A α hα hα',
      relClassOf_eq_homologyπ_cocycleOfK ℤ (TopCat.of X) C β hβ hβ', hcoe]
    exact relRelCupHMap_apply (TopCat.of X) A C 0 1 α β hα' hβ' hstar
  have htcm : tcmRelCup A C hA hC 0 1 (relClassOf ℤ (TopCat.of X) A α hα)
        (relClassOf ℤ (TopCat.of X) C β hβ)
      = tcmRelCupInv A C hA hC (0 + 1)
          ((HomologicalComplex.homologyπ (pdABCohR (R := ℤ) (TopCat.of X) A C) (0 + 1)).hom
            (cocycleOfK (pdABCohR (R := ℤ) (TopCat.of X) A C) γ hγ)) := by
    rw [tcmRelCup, tcmRelCupG_apply, hY]
  have hcomp : Work.Thom.relCohMap (ContinuousMap.id X) C (A ∪ C) (fun x hx => Or.inr hx) ℤ (0 + 1)
      = HomologicalComplex.homologyMap (pdABInclRelR (R := ℤ) (TopCat.of X) A C) (0 + 1)
        ≫ HomologicalComplex.homologyMap (pdABProjC ℤ (TopCat.of X) A C) (0 + 1) := by
    rw [show Work.Thom.relCohMap (ContinuousMap.id X) C (A ∪ C) (fun x hx => Or.inr hx) ℤ (0 + 1)
        = HomologicalComplex.homologyMap (relComplexMap (X₁ := TopCat.of X) (X₂ := TopCat.of X)
            ℤ C (A ∪ C) (TopCat.ofHom (ContinuousMap.id X)) (fun x hx => Or.inr hx)) (0 + 1)
        from rfl, ← pdABInclRelR_comp_pdABProjC (R := ℤ) (TopCat.of X) A C,
      HomologicalComplex.homologyMap_comp]
  have hproj : ((pdABProjC ℤ (TopCat.of X) A C).f (0 + 1)) γ = β := by
    rw [hγdef]
    apply Subtype.ext
    rw [pdABProjC_f_apply, pdABProjCLM_coe, starAB_coe, hαunit]
    simpa using (Work.Cohomology.cupUnit ℤ (TopCat.toSSet.obj (TopCat.of X)) β.1).1
  have hstarc : ((relComplex ℤ (TopCat.of X) C).d (0 + 1) (0 + 1 + 1)).hom
      ((pdABProjC ℤ (TopCat.of X) A C).f (0 + 1) γ) = 0 := by
    rw [hproj]
    simpa using hβ'
  rw [show Work.Thom.relCohMap (ContinuousMap.id X) C (A ∪ C) (fun x hx => Or.inr hx) ℤ 1
      = Work.Thom.relCohMap (ContinuousMap.id X) C (A ∪ C) (fun x hx => Or.inr hx) ℤ (0 + 1)
      from rfl]
  rw [htcm, hcomp, ModuleCat.hom_comp, LinearMap.comp_apply]
  refine Eq.trans (congrArg (fun z =>
      (HomologicalComplex.homologyMap (pdABProjC ℤ (TopCat.of X) A C) (0 + 1)).hom z)
    (tcmRelCupInv_spec (R := ℤ) A C hA hC (0 + 1)
      ((HomologicalComplex.homologyπ (pdABCohR (R := ℤ) (TopCat.of X) A C) (0 + 1)).hom
        (cocycleOfK (pdABCohR (R := ℤ) (TopCat.of X) A C) γ hγ)))) ?_
  rw [homologyMap_homologypi_cocycleOfK (R := ℤ) (φ := pdABProjC ℤ (TopCat.of X) A C) γ hγ hstarc]
  have hcoc : cocycleOfK (relComplex ℤ (TopCat.of X) C)
        ((pdABProjC ℤ (TopCat.of X) A C).f (0 + 1) γ) hstarc
      = cocycleOfK (relComplex ℤ (TopCat.of X) C) β hβ' :=
    cocycleOfK_congr hproj hstarc hβ'
  exact (congrArg (fun z =>
    (HomologicalComplex.homologyπ (relComplex ℤ (TopCat.of X) C) (0 + 1)).hom z) hcoc).trans
    (relClassOf_eq_homologyπ_cocycleOfK ℤ (TopCat.of X) C β hβ hβ').symm

end

end Work.Whitney

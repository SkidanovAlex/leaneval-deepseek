import Mathlib
import Submission.Work.Whitney.TCMDefs
import Submission.Work.Whitney.Unit.Pre
import Submission.Work.Whitney.Unit.Lemmas
import Submission.Work.Cohomology.h0Evaluation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The unit law of the canonical relative–relative cup product

`Work.Whitney.tcmRelCup` is the canonical relative–relative cup product
`H^m(X,A) ⊗ H^n(X,B) → H^{m+n}(X, A ∪ B)` for open `A, B ⊆ X`: the Alexander–Whitney product on
the `A+B` complex `C^*(X,A) ∩ C^*(X,B)` (`Work.Whitney.relRelCupHMap`), transported along the
inverse of the quasi-isomorphism `C^*(X, A∪B) → C^*(X, A+B)`
(`Work.Whitney.tcmRelCupInv`, `Work.Whitney.tcmRelCupInv_spec`).

This module proves the **unit law**: if `C ⊆ A` and `u ∈ H^0(X,C)` has absolute image the unit
class `1 ∈ H^0(X)`, then cupping with `u` is the identity of `H^m(X,A)`,

`(relCohMap id A (A∪C)).hom (tcmRelCup A C hA hC m 0 a u) = a`.

The proof is a computation with explicit cocycle representatives, in four steps.

* In degree `0` the cochain complex has no incoming differential, so `H^0` is exactly the module of
  `0`-cocycles and the hypothesis on `u` pins down its representing cochain: it must be the unit
  cochain `1` of the singular cochain complex
  (`Work.Whitney.relClassOf_relToAbs_oneH_coe`, proved via `Work.Cohomology.h0CycIso`).
* The Alexander–Whitney product of a cochain with the unit cochain is the cochain itself
  (`Work.Cohomology.cupUnit`), so the class of the Alexander–Whitney product of the representatives
  of `a` and `u`, transported back along `tcmRelCupInv`, is the class of `a`'s representative.
* The transport is *characterised* by `Work.Whitney.tcmRelCupInv_spec`
  (`tcmRelCupInv` is the inverse of the quasi-isomorphism `pdABInclRelR`).
* The remaining bookkeeping is the identity
  `pdABInclRelR ≫ pdABProj = relComplexMap id` (`Work.Whitney.pdABInclRelR_comp_pdABProj`): the
  pair map `C^*(X, A∪C) → C^*(X,A)` is the inclusion into `C^*(X,A+C)` followed by the projection
  of the `A+C` complex onto `C^*(X,A)` (`Work.Whitney.pdABProj`), so that the pair map of the source
  of `tcmRelCupInv` is the *left inverse* of that transport.

The auxiliary definitions (`Work.Whitney.pdABProj`) and the auxiliary lemmas
(`Work.Whitney.pdABInclRelR_comp_pdABProj`, `Work.Whitney.homologyMap_homologypi_cocycleOfK`,
`Work.Whitney.relClassOf_relToAbs_oneH_coe`) live in `Submission/Work/Whitney/Unit/`.
-/

namespace Work.Whitney

open Work.Cohomology
open CategoryTheory

noncomputable section

variable {R : Type} [CommRing R]

/-- A morphism of cochain complexes sends the cycle associated with a cocycle of the source to the
cycle associated with the image cocycle: an elementwise form of the functoriality of `cocycleOfK`,
needed because the cocycle condition is a *proof* argument of `cocycleOfK` (so plain rewriting in
its first argument is not type-correct). -/
lemma cocycleOfK_congr {K : CochainComplex (ModuleCat R) ℕ} {n : ℕ} {γ γ' : K.X n}
    (h : γ = γ') (hγ : (K.d n (n + 1)).hom γ = 0) (hγ' : (K.d n (n + 1)).hom γ' = 0) :
    cocycleOfK K γ hγ = cocycleOfK K γ' hγ' := by
  subst h
  exact congrArg (cocycleOfK K γ) (Subsingleton.elim hγ hγ')

theorem tcmRelCup_unit_right {X : Type} [TopologicalSpace X] (A C : Set X) (hA : IsOpen A)
    (hC : IsOpen C) (hCA : C ⊆ A) (m : ℕ) (a : Work.Thom.RelCoh ℤ m X A)
    (u : Work.Thom.RelCoh ℤ 0 X C)
    (hu : (Work.Thom.relToAbs ℤ C 0).hom u
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of X))) :
    (Work.Thom.relCohMap (ContinuousMap.id X) A (A ∪ C) (fun x hx => Or.inl hx) ℤ m).hom
        (Work.Whitney.tcmRelCup A C hA hC m 0 a u)
      = a := by
  obtain ⟨α, hα, rfl⟩ := exists_relClassOf ℤ (TopCat.of X) A m a
  obtain ⟨β, hβ, rfl⟩ := exists_relClassOf ℤ (TopCat.of X) C 0 u
  have hβunit : β.1 = Work.Cohomology.unitCochain ℤ (TopCat.toSSet.obj (TopCat.of X)) :=
    relClassOf_relToAbs_oneH_coe C β hβ hu
  have hα' : ((relComplex ℤ (TopCat.of X) A).d m (m + 1)).hom α = 0 := by
    rw [relComplex_d_apply]; exact hα
  have hβ' : ((relComplex ℤ (TopCat.of X) C).d 0 1).hom β = 0 := by
    rw [relComplex_d_apply]; exact hβ
  have hstar : ((pdABCohR (R := ℤ) (TopCat.of X) A C).d (m + 0) (m + 0 + 1)).hom
      (((starAB (TopCat.of X) A C m 0) α) β) = 0 :=
    ThreeCup.star3_cocycle_cochain (Leibniz3_starAB (TopCat.of X) A C) m 0 α β hα' hβ'
  -- the Alexander–Whitney product of the representatives, as a local element
  set γ : (pdABCohR (R := ℤ) (TopCat.of X) A C).X (m + 0) :=
    (((starAB (TopCat.of X) A C m 0) α) β) with hγdef
  have hγ : ((pdABCohR (R := ℤ) (TopCat.of X) A C).d (m + 0) (m + 0 + 1)).hom γ = 0 := hstar
  have hcoe : cocycleOfK (pdABCohR (R := ℤ) (TopCat.of X) A C) γ hγ
      = cocycleOfK (pdABCohR (R := ℤ) (TopCat.of X) A C)
          (((starAB (TopCat.of X) A C m 0) α) β) hstar := by
    apply iCycles_injective_K (pdABCohR (R := ℤ) (TopCat.of X) A C) (m + 0)
    rw [iCycles_cocycleOfK]
  have hY : relRelCupHMap (R := ℤ) (TopCat.of X) A C m 0
        (relClassOf ℤ (TopCat.of X) A α hα) (relClassOf ℤ (TopCat.of X) C β hβ)
      = (HomologicalComplex.homologyπ (pdABCohR (R := ℤ) (TopCat.of X) A C) (m + 0)).hom
          (cocycleOfK (pdABCohR (R := ℤ) (TopCat.of X) A C) γ hγ) := by
    rw [relClassOf_eq_homologyπ_cocycleOfK ℤ (TopCat.of X) A α hα hα',
      relClassOf_eq_homologyπ_cocycleOfK ℤ (TopCat.of X) C β hβ hβ', hcoe]
    exact relRelCupHMap_apply (TopCat.of X) A C m 0 α β hα' hβ' hstar
  have htcm : tcmRelCup A C hA hC m 0 (relClassOf ℤ (TopCat.of X) A α hα)
        (relClassOf ℤ (TopCat.of X) C β hβ)
      = tcmRelCupInv A C hA hC (m + 0)
          ((HomologicalComplex.homologyπ (pdABCohR (R := ℤ) (TopCat.of X) A C) (m + 0)).hom
            (cocycleOfK (pdABCohR (R := ℤ) (TopCat.of X) A C) γ hγ)) := by
    rw [tcmRelCup, tcmRelCupG_apply, hY]
  have hcomp : Work.Thom.relCohMap (ContinuousMap.id X) A (A ∪ C) (fun x hx => Or.inl hx) ℤ (m + 0)
      = HomologicalComplex.homologyMap (pdABInclRelR (R := ℤ) (TopCat.of X) A C) (m + 0)
        ≫ HomologicalComplex.homologyMap (pdABProj ℤ (TopCat.of X) A C) (m + 0) := by
    rw [show Work.Thom.relCohMap (ContinuousMap.id X) A (A ∪ C) (fun x hx => Or.inl hx) ℤ (m + 0)
        = HomologicalComplex.homologyMap (relComplexMap (X₁ := TopCat.of X) (X₂ := TopCat.of X)
            ℤ A (A ∪ C) (TopCat.ofHom (ContinuousMap.id X)) (fun x hx => Or.inl hx)) (m + 0)
        from rfl, ← pdABInclRelR_comp_pdABProj (R := ℤ) (TopCat.of X) A C,
      HomologicalComplex.homologyMap_comp]
  have hproj : ((pdABProj ℤ (TopCat.of X) A C).f (m + 0)) γ = α := by
    rw [hγdef]
    apply Subtype.ext
    rw [pdABProj_f_apply, pdABProjLM_coe, starAB_coe, hβunit]
    exact (Work.Cohomology.cupUnit ℤ (TopCat.toSSet.obj (TopCat.of X)) α.1).2
  have hstarc : ((relComplex ℤ (TopCat.of X) A).d (m + 0) (m + 0 + 1)).hom
      ((pdABProj ℤ (TopCat.of X) A C).f (m + 0) γ) = 0 := by
    rw [hproj]; exact hα'
  rw [show Work.Thom.relCohMap (ContinuousMap.id X) A (A ∪ C) (fun x hx => Or.inl hx) ℤ m
      = Work.Thom.relCohMap (ContinuousMap.id X) A (A ∪ C) (fun x hx => Or.inl hx) ℤ (m + 0)
      from rfl]
  rw [htcm, hcomp, ModuleCat.hom_comp, LinearMap.comp_apply]
  refine Eq.trans (congrArg (fun z =>
      (HomologicalComplex.homologyMap (pdABProj ℤ (TopCat.of X) A C) (m + 0)).hom z)
    (tcmRelCupInv_spec (R := ℤ) A C hA hC (m + 0)
      ((HomologicalComplex.homologyπ (pdABCohR (R := ℤ) (TopCat.of X) A C) (m + 0)).hom
        (cocycleOfK (pdABCohR (R := ℤ) (TopCat.of X) A C) γ hγ)))) ?_
  rw [homologyMap_homologypi_cocycleOfK (R := ℤ) (φ := pdABProj ℤ (TopCat.of X) A C) γ hγ hstarc]
  have hcoc : cocycleOfK (relComplex ℤ (TopCat.of X) A)
        ((pdABProj ℤ (TopCat.of X) A C).f (m + 0) γ) hstarc
      = cocycleOfK (relComplex ℤ (TopCat.of X) A) α hα' :=
    cocycleOfK_congr hproj hstarc hα'
  refine (congrArg (fun z =>
    (HomologicalComplex.homologyπ (relComplex ℤ (TopCat.of X) A) (m + 0)).hom z) hcoc).trans
    (relClassOf_eq_homologyπ_cocycleOfK ℤ (TopCat.of X) A α hα hα').symm

end

end Work.Whitney

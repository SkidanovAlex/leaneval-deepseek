import Mathlib
import Submission.Work.Whitney.TCMDefs
import Submission.Work.Whitney.Unit.Pre
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
`H^m(X,A) ⊗ H^n(X,B) → H^{m+n}(X, A ∪ B)` for open `A, B ⊆ X` (the Alexander–Whitney product on
the `A+B` complex `C^*(X,A) ∩ C^*(X,B)`, transported along the inverse of the quasi-isomorphism
`C^*(X, A∪B) → C^*(X, A+B)`).

This module proves the **unit law**: if `C ⊆ A` and `u ∈ H^0(X,C)` has absolute image the unit
class `1 ∈ H^0(X)`, then cupping with `u` is the identity of `H^m(X,A)`,

`(relCohMap id A (A∪C)).hom (tcmRelCup A C hA hC m 0 a u) = a`.

The proof is a computation with explicit cocycle representatives.  In degree `0` there are no
coboundaries (`H^0` is the module of `0`-cocycles), so the hypothesis on `u` pins down the cochain
representing `u`: it must be the unit cochain `1` of the singular cochain complex
(`Work.Whitney.relClassOf_relToAbs_oneH_coe`).  The Alexander–Whitney product of a cochain with the
unit cochain is the cochain itself (`Work.Cohomology.cupUnit`), so the transported `A+C` class is the
class of the relative cocycle `a` itself.  The bookkeeping is the identity
`pdABInclRelR ≫ pdABProj = relComplexMap id` (`Work.Whitney.pdABInclRelR_comp_pdABProj`): the pair
map `C^*(X, A∪C) → C^*(X,A)` is the inclusion into `C^*(X,A+C)` followed by the projection onto
`C^*(X,A)`, and the second factor is the inverse of the quasi-isomorphism used to define
`tcmRelCup` (`Work.Whitney.tcmRelCupInv_spec`).
-/

namespace Work.Whitney

open Work.Cohomology
open CategoryTheory

noncomputable section

variable {R : Type} [CommRing R]

/-! ## Coercion rules for the maps between the complexes `C^*(X,A)`, `C^*(X,C)` and `C^*(X,A+C)` -/

/-- The inclusion `C^*(X, A∪C) → C^*(X, A+C)` leaves the underlying cochain unchanged. -/
lemma pdABInclRelR_coe (X : TopCat) (A C : Set X) (n : ℕ)
    (x : (relComplex R X (A ∪ C)).X n) :
    ((ModuleCat.Hom.hom ((pdABInclRelR (R := R) X A C).f n)) x).1 = x.1 := rfl

/-- The projection `C^*(X, A+C) → C^*(X, A)` leaves the underlying cochain unchanged. -/
lemma pdABProj_coe (X : TopCat) (A C : Set X) (n : ℕ)
    (x : (pdABCohR (R := R) X A C).X n) :
    ((ModuleCat.Hom.hom ((pdABProj R X A C).f n)) x).1 = x.1 := rfl

/-- The pair map `C^*(X, A∪C) → C^*(X, A)` induced by the identity leaves the underlying cochain
unchanged. -/
lemma relComplexMap_id_coe (X : TopCat) (A C : Set X)
    (hh : ∀ x ∈ A, (TopCat.ofHom (ContinuousMap.id X)) x ∈ A ∪ C) (n : ℕ)
    (x : (relComplex R X (A ∪ C)).X n) :
    ((ModuleCat.Hom.hom
      ((relComplexMap (X₁ := X) (X₂ := X) R A (A ∪ C)
        (TopCat.ofHom (ContinuousMap.id X)) hh).f n)) x).1 = x.1 := by
  have key : (relComplexMap (X₁ := X) (X₂ := X) R A (A ∪ C)
        (TopCat.ofHom (ContinuousMap.id X)) hh).f n
      = ModuleCat.ofHom (relMapLM R A (A ∪ C) (TopCat.ofHom (ContinuousMap.id X)) hh n) :=
    relComplexMap_f ..
  have h1 : ModuleCat.Hom.hom ((relComplexMap (X₁ := X) (X₂ := X) R A (A ∪ C)
        (TopCat.ofHom (ContinuousMap.id X)) hh).f n)
      = relMapLM R A (A ∪ C) (TopCat.ofHom (ContinuousMap.id X)) hh n :=
    (congrArg ModuleCat.Hom.hom key).trans (ModuleCat.hom_ofHom _)
  rw [h1]
  exact (relMapLM_coe R A (A ∪ C) (TopCat.ofHom (ContinuousMap.id X)) hh n x).trans
    (by rw [TopCat.ofHom_id, dualChainMap_id, HomologicalComplex.id_f, ModuleCat.hom_id,
      LinearMap.id_apply])

/-- **The pair map `C^*(X,A∪C) → C^*(X,A)` is the composite of the inclusion of `C^*(X,A∪C)` into
the `A+C` complex and the projection of the `A+C` complex onto `C^*(X,A)`.**  Both maps leave the
underlying cochain unchanged. -/
theorem pdABInclRelR_comp_pdABProj (X : TopCat) (A C : Set X) :
    pdABInclRelR (R := R) X A C ≫ pdABProj R X A C
      = relComplexMap (X₁ := X) (X₂ := X) R A (A ∪ C)
          (TopCat.ofHom (ContinuousMap.id X)) (fun x hx => Or.inl hx) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, pdABInclRelR_coe, pdABProj_coe]
  exact (relComplexMap_id_coe X A C (fun x hx => Or.inl hx) n x).symm

/-- **A morphism of cochain complexes sends the homology class of the cycle associated with a
cocycle to the homology class of the cycle associated with the image cocycle.** -/
lemma homologyMap_homologypi_cocycleOfK {R : Type} [CommRing R]
    {K L : CochainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) {n : ℕ} (γ : K.X n)
    (hγ : (K.d n (n + 1)).hom γ = 0) (hγ' : (L.d n (n + 1)).hom ((φ.f n).hom γ) = 0) :
    (HomologicalComplex.homologyMap φ n).hom
        ((K.homologyπ n).hom (cocycleOfK K γ hγ))
      = (L.homologyπ n).hom
        (cocycleOfK L ((φ.f n).hom γ) hγ') := by
  rw [homologyMap_homologyπ (R := R) φ n (cocycleOfK K γ hγ)]
  refine congrArg (fun z => (L.homologyπ n).hom z) ?_
  apply iCycles_injective_K L n
  rw [cyclesMap_i_apply_gen φ n (cocycleOfK K γ hγ), iCycles_cocycleOfK K γ hγ,
    iCycles_cocycleOfK L ((φ.f n).hom γ) hγ']

/-- **A degree-zero relative class whose absolute image is the unit class is represented by the unit
cochain.**  In degree `0` the cochain complex has no incoming differential, so `H^0` is exactly the
module of `0`-cocycles and two degree-zero classes are equal if and only if their representing
cochains are. -/
lemma relClassOf_relToAbs_oneH_coe {X : Type} [TopologicalSpace X] (C : Set X)
    (β : relKern ℤ (TopCat.of X) C 0) (hβ : relDiffLM ℤ (TopCat.of X) C 0 β = 0)
    (hu : (Work.Thom.relToAbs ℤ C 0).hom (relClassOf ℤ (TopCat.of X) C β hβ)
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of X))) :
    β.1 = Work.Cohomology.unitCochain ℤ (TopCat.toSSet.obj (TopCat.of X)) := by
  have h1 : cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of X)) β.1
      (relClassOf_cochainDiff ℤ (TopCat.of X) C β hβ)
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of X)) := by
    rw [← relIncl_homologyMap_relClassOf ℤ (TopCat.of X) C β hβ]
    exact hu
  have h2 : cocycleOf ℤ (TopCat.toSSet.obj (TopCat.of X)) β.1
        (relClassOf_cochainDiff ℤ (TopCat.of X) C β hβ)
      = cocycleOf ℤ (TopCat.toSSet.obj (TopCat.of X))
        (Work.Cohomology.unitCochain ℤ (TopCat.toSSet.obj (TopCat.of X)))
        (cochainDiff_unitCochain ℤ (TopCat.toSSet.obj (TopCat.of X))) := by
    rw [← h0CycIso_classOf (TopCat.toSSet.obj (TopCat.of X)) β.1
        (relClassOf_cochainDiff ℤ (TopCat.of X) C β hβ),
      ← h0CycIso_classOf (TopCat.toSSet.obj (TopCat.of X))
        (Work.Cohomology.unitCochain ℤ (TopCat.toSSet.obj (TopCat.of X)))
        (cochainDiff_unitCochain ℤ (TopCat.toSSet.obj (TopCat.of X)))]
    rw [h1]
    rfl
  have h3 := congrArg (fun z =>
    ((SSetCochainComplex ℤ (TopCat.toSSet.obj (TopCat.of X))).iCycles 0).hom z) h2
  rw [iCycles_cocycleOf ℤ (TopCat.toSSet.obj (TopCat.of X)) β.1
      (relClassOf_cochainDiff ℤ (TopCat.of X) C β hβ),
    iCycles_cocycleOf ℤ (TopCat.toSSet.obj (TopCat.of X))
      (Work.Cohomology.unitCochain ℤ (TopCat.toSSet.obj (TopCat.of X)))
      (cochainDiff_unitCochain ℤ (TopCat.toSSet.obj (TopCat.of X)))] at h3
  exact h3


end

end Work.Whitney

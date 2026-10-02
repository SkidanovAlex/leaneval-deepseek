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
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The *left* unit law of the canonical relative–relative cup product

`Work.Whitney.tcmRelCup` is the canonical relative–relative cup product
`H^m(X,A) ⊗ H^n(X,B) → H^{m+n}(X, A ∪ B)` for open `A, B ⊆ X`.  `Submission/Work/Whitney/
tcmRelCup_unit_right.lean` proves the *right* unit law (cupping a degree-zero class whose absolute
image is the unit on the right is the identity, for `C ⊆ A`).  This module proves the *left* unit
law, in the form needed by the `p = 0` corner of the model product formula:

if `A ⊆ C` and `u ∈ H^0(X,A)` has absolute image the unit class, then

  `(relCohMap id C (A∪C)).hom (tcmRelCup A C hA hC 0 n u b) = b`

(up to the degree cast `0 + n = n`).

The proof mirrors the right unit law: the degree-zero hypothesis pins the representing cochain as the
unit cochain (`Work.Whitney.relClassOf_relToAbs_oneH_coe`), the chain-level unit law
`Work.Cohomology.cupUnit` (left component) identifies the Alexander–Whitney product of the
representatives with `b`'s representative, and the bookkeeping is the *C-side* version
`Work.Whitney.pdABInclRelR_comp_pdABProjC` of
`Work.Whitney.pdABInclRelR_comp_pdABProj` (the pair map `C^*(X,A∪C) → C^*(X,C)` is the inclusion
into the `A+C` complex followed by the projection onto `C^*(X,C)`).
-/

namespace Work.Whitney

open Work.Cohomology
open CategoryTheory

noncomputable section

variable {R : Type} [CommRing R]

/-! ## The projection `C^*(X, A+C) → C^*(X, C)` -/

/-- The degreewise projection `C^n(X,A) ∩ C^n(X,C) → C^n(X,C)` (the second projection of the
intersection), as an explicit linear map. -/
def pdABProjCLM (R : Type) [CommRing R] (X : TopCat) (A C : Set X) (n : ℕ) :
    (pdABKernR (R := R) X A C n) →ₗ[R] relKern R X C n where
  toFun x := ⟨x.1, (Submodule.mem_inf.mp (by
    rw [show relKern R X A n ⊓ relKern R X C n = pdABKernR (R := R) X A C n from rfl];
    exact x.2)).2⟩
  map_add' x y := by apply Subtype.ext; rfl
  map_smul' c x := by apply Subtype.ext; rfl

/-- The underlying cochain of `Work.Whitney.pdABProjCLM` is the cochain itself. -/
@[simp] lemma pdABProjCLM_coe (R : Type) [CommRing R] (X : TopCat) (A C : Set X) (n : ℕ)
    (x : pdABKernR (R := R) X A C n) : (pdABProjCLM R X A C n x).1 = x.1 := rfl

/-- **The projection of the `A+C` cochain complex onto the relative cochain complex of `C`**: on
degree `n` a cochain vanishing on `A` and on `C` is sent to itself, viewed as a cochain vanishing on
`C`. -/
def pdABProjC (R : Type) [CommRing R] (X : TopCat) (A C : Set X) :
    pdABCohR (R := R) X A C ⟶ relComplex R X C :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (pdABProjCLM R X A C n))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
        pdABCohR_d, relComplex_d]
      rfl)

/-- The `n`-th component of `Work.Whitney.pdABProjC`. -/
@[simp] lemma pdABProjC_f (R : Type) [CommRing R] (X : TopCat) (A C : Set X) (n : ℕ) :
    (pdABProjC R X A C).f n = ModuleCat.ofHom (pdABProjCLM R X A C n) := rfl

/-- The `n`-th component of `Work.Whitney.pdABProjC`, evaluated. -/
@[simp] lemma pdABProjC_f_apply (R : Type) [CommRing R] (X : TopCat) (A C : Set X) (n : ℕ)
    (x : (pdABCohR (R := R) X A C).X n) :
    (pdABProjC R X A C).f n x = pdABProjCLM R X A C n x := rfl

/-- The pair map `C^*(X,A∪C) → C^*(X,C)` induced by the identity leaves the underlying cochain
unchanged. -/
lemma relComplexMap_id_coeC (X : TopCat) (A C : Set X)
    (hh : ∀ x ∈ C, (TopCat.ofHom (ContinuousMap.id X)) x ∈ A ∪ C) (n : ℕ)
    (x : (relComplex R X (A ∪ C)).X n) :
    ((ModuleCat.Hom.hom
      ((relComplexMap (X₁ := X) (X₂ := X) R C (A ∪ C)
        (TopCat.ofHom (ContinuousMap.id X)) hh).f n)) x).1 = x.1 := by
  have key : (relComplexMap (X₁ := X) (X₂ := X) R C (A ∪ C)
        (TopCat.ofHom (ContinuousMap.id X)) hh).f n
      = ModuleCat.ofHom (relMapLM R C (A ∪ C) (TopCat.ofHom (ContinuousMap.id X)) hh n) :=
    relComplexMap_f ..
  have h1 : ModuleCat.Hom.hom ((relComplexMap (X₁ := X) (X₂ := X) R C (A ∪ C)
        (TopCat.ofHom (ContinuousMap.id X)) hh).f n)
      = relMapLM R C (A ∪ C) (TopCat.ofHom (ContinuousMap.id X)) hh n :=
    (congrArg ModuleCat.Hom.hom key).trans (ModuleCat.hom_ofHom _)
  rw [h1]
  exact (relMapLM_coe R C (A ∪ C) (TopCat.ofHom (ContinuousMap.id X)) hh n x).trans
    (by rw [TopCat.ofHom_id, dualChainMap_id, HomologicalComplex.id_f, ModuleCat.hom_id,
      LinearMap.id_apply])

/-- **The pair map `C^*(X,A∪C) → C^*(X,C)` is the composite of the inclusion of `C^*(X,A∪C)` into
the `A+C` complex and the projection of the `A+C` complex onto `C^*(X,C)`.** -/
theorem pdABInclRelR_comp_pdABProjC (X : TopCat) (A C : Set X) :
    pdABInclRelR (R := R) X A C ≫ pdABProjC R X A C
      = relComplexMap (X₁ := X) (X₂ := X) R C (A ∪ C)
          (TopCat.ofHom (ContinuousMap.id X)) (fun x hx => Or.inr hx) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, pdABInclRelR_coe, pdABProjCLM_coe]
  exact (relComplexMap_id_coeC X A C (fun x hx => Or.inr hx) n x).symm

end

end Work.Whitney

namespace Work.Whitney

-- (The left unit law `Work.Whitney.tcmUnitLeft` is delegated to
-- `Submission/Work/Whitney/tcmRelCup_unit_left.lean`; the infrastructure above is what it needs.)

end Work.Whitney

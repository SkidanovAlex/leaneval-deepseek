import Mathlib
import Submission.Work.Whitney.TCMDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The projection `C^*(X, A+C) → C^*(X, A)`

For the unit law of the canonical relative–relative cup product
(`Work.Whitney.tcmRelCup_unit_right`) one compares the canonical cup product with the explicit
chain-level projection of the `A+C` complex (the degreewise intersection
`C^n(X,A) ∩ C^n(X,C)`) onto the relative complex of `A`.

This module contains that projection and its defining computation rules; it is the vocabulary shared
by the other files of this stretch (`Submission/Work/Whitney/Unit/`).
-/

namespace Work.Whitney

open Work.Cohomology
open CategoryTheory

noncomputable section

variable {R : Type} [CommRing R]

/-- The degreewise projection `C^n(X,A) ∩ C^n(X,C) → C^n(X,A)` (the first projection of the
intersection), as an explicit linear map. -/
def pdABProjLM (R : Type) [CommRing R] (X : TopCat) (A C : Set X) (n : ℕ) :
    (pdABKernR (R := R) X A C n) →ₗ[R] relKern R X A n where
  toFun x := ⟨x.1, (Submodule.mem_inf.mp (by
    rw [show relKern R X A n ⊓ relKern R X C n = pdABKernR (R := R) X A C n from rfl]; exact x.2)).1⟩
  map_add' x y := by apply Subtype.ext; rfl
  map_smul' c x := by apply Subtype.ext; rfl

/-- The underlying cochain of `Work.Whitney.pdABProjLM` is the cochain itself. -/
@[simp] lemma pdABProjLM_coe (R : Type) [CommRing R] (X : TopCat) (A C : Set X) (n : ℕ)
    (x : pdABKernR (R := R) X A C n) : (pdABProjLM R X A C n x).1 = x.1 := rfl

/-- The underlying cochain of `Work.Whitney.pdABProjLM`, in the form of the inclusion of cochains. -/
lemma pdABProjLM_coe' (R : Type) [CommRing R] (X : TopCat) (A C : Set X) (n : ℕ)
    (x : pdABKernR (R := R) X A C n) :
    ((pdABProjLM R X A C n x : relKern R X A n) : (singularCochainComplex R X).X n) = x.1 := rfl

/-- **The projection of the `A+C` cochain complex onto the relative cochain complex of `A`**: on
degree `n` a cochain vanishing on `A` and on `C` is sent to itself, viewed as a cochain vanishing on
`A`.  It is a map of cochain complexes because the differential of the relative complex is the
restriction of the differential of the ambient complex. -/
def pdABProj (R : Type) [CommRing R] (X : TopCat) (A C : Set X) :
    pdABCohR (R := R) X A C ⟶ relComplex R X A :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (pdABProjLM R X A C n))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
        pdABCohR_d, relComplex_d]
      rfl)

/-- The `n`-th component of `Work.Whitney.pdABProj`. -/
@[simp] lemma pdABProj_f (R : Type) [CommRing R] (X : TopCat) (A C : Set X) (n : ℕ) :
    (pdABProj R X A C).f n = ModuleCat.ofHom (pdABProjLM R X A C n) := rfl

/-- The `n`-th component of `Work.Whitney.pdABProj`, evaluated. -/
@[simp] lemma pdABProj_f_apply (R : Type) [CommRing R] (X : TopCat) (A C : Set X) (n : ℕ)
    (x : (pdABCohR (R := R) X A C).X n) :
    (pdABProj R X A C).f n x = pdABProjLM R X A C n x := rfl

end

end Work.Whitney

import Mathlib
import Submission.Work.Serre.relCohMV_les_rat
import Submission.Work.Serre.MVCohRatDefs
import Submission.Work.Serre.fiveLemma_LES_first
import Submission.Work.Serre.boundedFiveLemmaLES
import Submission.Work.Serre.bijective_mixedCup_of_openCover_zero
import Submission.Work.Serre.bijAssembly
import Submission.Work.Serre.mvGlueTwo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.MVGlue

/-- Two `eqToHom`s with the same source and target are equal. -/
theorem eqToHom_proof_irrel {C : Type*} [Category C] {a b : C} (h₁ h₂ : a = b) :
    CategoryTheory.eqToHom h₁ = CategoryTheory.eqToHom h₂ := by
  rw [Subsingleton.elim h₁ h₂]

/-- `eqToHom` depends on its equation only through its type. -/
theorem eqToHom_congrArg_proof_irrel {C : Type*} [Category C] (f : ℕ → C) {a b : ℕ}
    (h₁ h₂ : a = b) :
    CategoryTheory.eqToHom (congrArg f h₁) = CategoryTheory.eqToHom (congrArg f h₂) := by
  rw [Subsingleton.elim h₁ h₂]



theorem glueCupIso {X : Type} [TopologicalSpace X] (A : Set X)
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (n₀ K : ℕ) (U₀ : Work.Thom.RelCoh ℚ n₀ X A)
    (hdelta : ∀ (m : ℕ) (x : Work.Serre.mvCohUV (TopCat.of X) (∅ : Set X) U V m),
      (Work.Thom.mixedCupC ℚ A (m + 1) n₀)
          ((Work.Thom.relToAbs ℚ (∅ : Set X) (m + 1)).hom
            ((Work.Serre.mvDelta (TopCat.of X) (∅ : Set X) U V hU hV hcov m).hom x)) U₀
        = (CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh ℚ j (TopCat.of X) A)
              (by omega : (m + n₀) + 1 = (m + 1) + n₀))).hom
            ((Work.Serre.mvDelta (TopCat.of X) A U V hU hV hcov (m + n₀)).hom
              ((Work.Thom.mixedCupC ℚ {y : ↥(U ∩ V) | (y : X) ∈ A} m n₀)
                ((Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) m).hom x)
                ((Work.Thom.relCohMap
                  (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U ∩ V), X))
                  {y : ↥(U ∩ V) | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀))))
    (hlocU : ∀ m : ℕ, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥U =>
      (Work.Thom.mixedCupC ℚ {y : ↥U | (y : X) ∈ A} m n₀) x
        ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X))
          {y : ↥U | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀)))
    (hlocV : ∀ m : ℕ, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥V =>
      (Work.Thom.mixedCupC ℚ {y : ↥V | (y : X) ∈ A} m n₀) x
        ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, X))
          {y : ↥V | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀)))
    (hlocUV : ∀ m : ℕ, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥(U ∩ V) =>
      (Work.Thom.mixedCupC ℚ {y : ↥(U ∩ V) | (y : X) ∈ A} m n₀) x
        ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U ∩ V), X))
          {y : ↥(U ∩ V) | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀))) :
    ∀ m : ℕ, 1 ≤ m → m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m X =>
      (Work.Thom.mixedCupC ℚ A m n₀) x U₀) := by
  -- The boundary square is taken from the repaired engine `Work.Serre.mvDelta_vertM_eq`
  -- (this file's own proof of it no longer matches the current spelling of
  -- `Work.Serre.mvDeltaCupMixedAux`; see the session-7 notes in `Work.Serre.thomCupInj`).
  exact Work.Serre.bijective_mixedCup_of_openCover_aux A U V hU hV hcov n₀ K U₀
    hlocU hlocV hlocUV
    (Work.Serre.mvDelta_vertM_eq (TopCat.of X) A U V hU hV hcov n₀ U₀)

end Work.Serre.MVGlue

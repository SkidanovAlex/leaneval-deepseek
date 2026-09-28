import Mathlib
import Submission.Work.Serre.bijAssembly
import Submission.Work.Serre.mvDeltaCupMixedAux

/-!
# The two-piece Mayer–Vietoris gluing of the cup map

`Work.Serre.bijective_mixedCup_of_openCover_aux` (`Submission/Work/Serre/bijAssembly.lean`) reduces
the local-to-global gluing of the cup-map bijectivity over an open cover `X = U ∪ V` to the single
*boundary square* (`Hdelta`)

  `δ_∅ ≫ vertM = vertQ ≫ δ_A`

of the Mayer–Vietoris ladder.  The file `Submission/Work/Serre/MVGlue/glueCupIso.lean` supplies that
square from the pointwise Leibniz rule `Work.Serre.mvDeltaCupMixedAux`, but its final `rw` no longer
matches the current spelling of `mvDeltaCupMixedAux` (the `U₀ovl` restatement `U₀ovl_eq_relCohMapAux`
of `bijAssembly.lean` has to be applied first, and the `eqToHom` carriers have to be identified by
proof irrelevance).  This file redoes that step, so that the gluing is available again:

* `Work.Serre.mvDelta_vertM_eq` — the boundary square, from `mvDeltaCupMixedAux`;
* `Work.Serre.cupBijective_of_twoPieceCover` — the gluing.

The statement below is the engine used by `Submission/Work/Serre/mvGlueFinite.lean` (the finite-cover
induction) and hence by the cover-based route to the Thom injectivity.
-/

set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- `eqToHom` depends on its equation only through its type (proof irrelevance). -/
theorem eqToHom_congrArg_proof_irrel {C : Type*} [Category C] (f : ℕ → C) {a b : ℕ}
    (h₁ h₂ : a = b) :
    CategoryTheory.eqToHom (congrArg f h₁) = CategoryTheory.eqToHom (congrArg f h₂) := by
  rw [Subsingleton.elim h₁ h₂]

/-- **The boundary square of the Mayer–Vietoris ladder for the mixed cup product.**

For an open cover `X = U ∪ V`, a relative class `U₀ ∈ H^{n₀}(X,A;ℚ)` and every degree `m`, the
connecting map `δ` of the rational relative Mayer–Vietoris sequence commutes with the cup map:
`δ_∅ ≫ (· ⌣ U₀) = (· ⌣ U₀|_{U∩V}) ≫ δ_A`.  This is the hypothesis `Hdelta` of
`Work.Serre.bijective_mixedCup_of_openCover_aux`, proved here from the pointwise Leibniz rule
`Work.Serre.mvDeltaCupMixedAux`. -/
theorem mvDelta_vertM_eq (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n₀ : ℕ) (U₀ : Work.Thom.RelCoh ℚ n₀ X A) (m : ℕ) :
    CategoryTheory.CategoryStruct.comp (mvDelta X (∅ : Set X) U V hU hV hcov m)
        (vertM X A n₀ U₀ (m + 1))
      = CategoryTheory.CategoryStruct.comp (vertQ X A U V n₀ U₀ m)
          (mvDeltaShift X A U V hU hV hcov n₀ m) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hL : (ModuleCat.Hom.hom (CategoryTheory.CategoryStruct.comp
        (mvDelta X (∅ : Set X) U V hU hV hcov m) (vertM X A n₀ U₀ (m + 1)))) x
      = (Work.Thom.mixedCupC ℚ A (m + 1) n₀)
          ((Work.Thom.relToAbs ℚ (∅ : Set X) (m + 1)).hom
            ((mvDelta X (∅ : Set X) U V hU hV hcov m).hom x)) U₀ := by
    rw [ModuleCat.hom_comp, LinearMap.comp_apply]
    rfl
  have hR : (ModuleCat.Hom.hom (CategoryTheory.CategoryStruct.comp
        (vertQ X A U V n₀ U₀ m) (mvDeltaShift X A U V hU hV hcov n₀ m))) x
      = (CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh ℚ j X A)
            (mvShiftEq m n₀))).hom
          ((mvDelta X A U V hU hV hcov (m + n₀)).hom
            ((Work.Thom.mixedCupC ℚ {y : ↥(U ∩ V) | (y : X) ∈ A} m n₀)
              ((Work.Thom.relToAbs ℚ (∅ : Set ↥(U ∩ V)) m).hom x)
              (U₀ovl X A U V n₀ U₀))) := by
    rw [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [show (mvDeltaShift X A U V hU hV hcov n₀ m)
        = mvDelta X A U V hU hV hcov (m + n₀) ≫
          CategoryTheory.eqToHom (congrArg (fun j => Work.Thom.RelCoh ℚ j X A)
            (mvShiftEq m n₀)) from rfl]
    rw [ModuleCat.hom_comp, LinearMap.comp_apply]
    rfl
  rw [hL, hR, Work.Serre.U₀ovl_eq_relCohMapAux]
  rw [eqToHom_congrArg_proof_irrel (fun j => Work.Thom.RelCoh ℚ j X A)
      (by omega : (m + n₀) + 1 = (m + 1) + n₀) (mvShiftEq m n₀)]
  exact Work.Serre.mvDeltaCupMixedAux X A U V hU hV hcov n₀ U₀ m x

/-- **The two-piece Mayer–Vietoris gluing.**  If the cup map with `U₀` is bijective in the range on
each of the three pieces `U`, `V`, `U ∩ V` of an open cover `X = U ∪ V`, then it is bijective in the
range on `X` (in degrees `m ≥ 1`, which is all that is needed for the Thom statements). -/
theorem cupBijective_of_twoPieceCover {X : Type} [TopologicalSpace X] (A : Set X)
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (n₀ K : ℕ) (U₀ : Work.Thom.RelCoh ℚ n₀ X A)
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
      (Work.Thom.mixedCupC ℚ A m n₀) x U₀) :=
  bijective_mixedCup_of_openCover_aux A U V hU hV hcov n₀ K U₀ hlocU hlocV hlocUV
    (fun m => mvDelta_vertM_eq (TopCat.of X) A U V hU hV hcov n₀ U₀ m)

end

end Work.Serre

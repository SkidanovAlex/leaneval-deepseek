/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.GaloisIdelesAction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The action of `Gal(L/K)` on principal idèles

The group `Gal(L/K) = (L ≃ₐ[K] L)` acts on the idèle group `𝕀 L` by
`(σ · x)_w = σ_*(x_{σ⁻¹ w})`, where `σ_* : L_w ≃+* L_{σ w}` is the canonical isomorphism of local
fields induced by `σ` (`NK.GlobalCFT.Idele.smul_apply`).

This file records the compatibility of that action with the diagonal embedding `Lˣ → 𝕀 L`: the
translate of the principal idèle attached to `y ∈ Lˣ` is the principal idèle attached to the
translate `σ y` of `y`:

`σ • principalIdele L y = principalIdele L (Units.map σ.toMonoidHom y)`.

At a place `w` this is the statement that the canonical local isomorphism
`Place.localRingEquiv σ⁻¹ w : L_w ≃+* L_{σ⁻¹ w}` is compatible with the embeddings of `L`, so
that it identifies `σ y` with `y` (`Place.localRingEquiv_algebraMap`).

## Main results

* `NK.GlobalCFT.Galois.globalCFT_localRingEquiv_symm_algebraMap`: the inverse local isomorphism
  sends `x` back to `σ x`;
* `NK.GlobalCFT.Galois.globalCFT_smul_principalIdele`: the action on principal idèles.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct

noncomputable section

namespace NK.GlobalCFT.Galois

open NK.GlobalCFT

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The inverse of the canonical local isomorphism `Place.localRingEquiv σ⁻¹ w : L_w ≃+* L_{σ⁻¹ w}`
is compatible with the embeddings of `L`: an element embedded in `L_{σ⁻¹ w}` is sent back to the
element embedded in `L_w` after applying `σ`. -/
lemma globalCFT_localRingEquiv_symm_algebraMap (σ : L ≃ₐ[K] L) (w : NK.GlobalCFT.Place L)
    (x : L) :
    (NK.GlobalCFT.Place.localRingEquiv σ⁻¹ w).symm
        (algebraMap L (NK.GlobalCFT.Place.localField L (σ⁻¹ • w)) x) =
      algebraMap L (NK.GlobalCFT.Place.localField L w) (σ x) := by
  -- Applying the inverse isomorphism to both sides, the statement is the compatibility of
  -- `Place.localRingEquiv σ⁻¹ w` with the embeddings of `L`, together with `σ⁻¹ (σ x) = x`.
  have h : (NK.GlobalCFT.Place.localRingEquiv σ⁻¹ w)
      (algebraMap L (NK.GlobalCFT.Place.localField L w) (σ x))
      = algebraMap L (NK.GlobalCFT.Place.localField L (σ⁻¹ • w)) x := by
    have h0 := NK.GlobalCFT.Place.localRingEquiv_algebraMap (σ⁻¹) w (σ x)
    simpa using h0
  rw [← h, RingEquiv.symm_apply_apply]

/-- The action of `Gal(L/K)` on the idèle group is compatible with the diagonal embedding: the
translate of the principal idèle attached to `y ∈ Lˣ` is the principal idèle attached to `σ y`. -/
theorem globalCFT_smul_principalIdele {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L) (y : Lˣ) :
    σ • NK.GlobalCFT.Idele.principalIdele L y =
      NK.GlobalCFT.Idele.principalIdele L (Units.map σ.toMonoidHom y) := by
  -- Compare the components at an arbitrary place `w`.
  refine NK.GlobalCFT.Idele.ext fun w => ?_
  rw [NK.GlobalCFT.Idele.smul_apply, NK.GlobalCFT.Idele.principalIdele_apply,
    NK.GlobalCFT.Idele.principalIdele_apply]
  refine Units.ext ?_
  show (NK.GlobalCFT.Place.localRingEquiv σ⁻¹ w).symm
      (algebraMap L (NK.GlobalCFT.Place.localField L (σ⁻¹ • w)) (y : L)) =
    algebraMap L (NK.GlobalCFT.Place.localField L w) (σ (y : L))
  exact globalCFT_localRingEquiv_symm_algebraMap σ w (y : L)

end NK.GlobalCFT.Galois

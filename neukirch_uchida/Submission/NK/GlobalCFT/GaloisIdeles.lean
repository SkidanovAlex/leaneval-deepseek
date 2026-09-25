/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFT.GaloisAction
import Submission.NK.GlobalCFT.Galois.globalCFT_exists_localRingEquiv_smul

/-!
# The action of `Gal(L/K)` on the idèles

For a finite extension `L / K` the group `Gal(L/K) = (L ≃ₐ[K] L)` acts on the idèle group `𝕀 L`
by `(σ · x)_w = σ_*(x_{σ⁻¹ w})`, where `σ_* : L_w ≃+* L_{σ w}` is the canonical isomorphism of
local fields induced by `σ`.  Since `σ_*` maps `𝒪_vˣ` onto `𝒪_{σv}ˣ`, the action preserves the
restricted product.

## Main definitions

* `NK.GlobalCFT.Place.localRingEquiv`: the canonical local isomorphism `L_v ≃+* L_{σ v}`.

## Main results

* `NK.GlobalCFT.Place.localRingEquiv_algebraMap`: the local isomorphism is compatible with the
  embeddings of `L`;
* `NK.GlobalCFT.Place.localRingEquiv_mem_localUnits`: it maps local units to local units.

The `SMul (L ≃ₐ[K] L) (𝕀 L)` instance (and its descent to `C_L`) uses the eventual-membership
lemma `NK.GlobalCFT.Galois.globalCFT_eventually_smul_mem` and the composition law
`NK.GlobalCFT.Galois.globalCFT_localRingEquiv_comp`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT

namespace Place

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The canonical isomorphism of local fields `L_v ≃+* L_{σ v}` induced by `σ : L ≃ₐ[K] L`:
the archimedean case is `NK.GlobalCFT.Galois.globalCFT_infiniteCongrEquiv` and the
nonarchimedean case is `NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv`. -/
noncomputable def localRingEquiv (σ : L ≃ₐ[K] L) :
    (v : Place L) → (localField L v) ≃+* (localField L (σ • v))
  | Sum.inl w => NK.GlobalCFT.Galois.globalCFT_infiniteCongrEquiv σ w
  | Sum.inr q => NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv σ q

/-- The local isomorphism is compatible with the embeddings of `L`. -/
theorem localRingEquiv_algebraMap (σ : L ≃ₐ[K] L) (v : Place L) (x : L) :
    localRingEquiv σ v (algebraMap L (localField L v) x) =
      algebraMap L (localField L (σ • v)) (σ x) := by
  cases v with
  | inl w =>
      exact NK.GlobalCFT.Galois.globalCFT_infiniteCongrEquiv_algebraMap σ w x
  | inr q =>
      exact NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv_algebraMap σ q x

/-- The local isomorphism maps local units to local units. -/
theorem localRingEquiv_mem_localUnits (σ : L ≃ₐ[K] L) (v : Place L)
    (u : (localField L v)ˣ) :
    u ∈ localUnits L v ↔
      Units.map (localRingEquiv σ v).toMonoidHom u ∈ localUnits L (σ • v) := by
  cases v with
  | inl w => simp [localRingEquiv, localUnits_ofInfinite]
  | inr q =>
      exact NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv_localUnits σ q u

end Place

end NK.GlobalCFT

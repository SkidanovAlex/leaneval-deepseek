/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.GaloisIdelesAction

/-!
# `Gal(L/K)` acts by group endomorphisms on the idèles

The idèle group `𝕀 L = Πʳ v, [(L_v)ˣ, (𝒪_v)ˣ]` is a restricted product, hence a subtype of the
product `Π v, (L_v)ˣ`, and its multiplication is the pointwise one:
`Idele.mul_apply`.  The action of `σ : Gal(L/K) = (L ≃ₐ[K] L)` on `𝕀 L` is componentwise in the
sense that `(σ • x) w = σ_*(x_{σ⁻¹ w})` (`Idele.smul_apply`), where `σ_*` is the canonical local
isomorphism, which is a *multiplicative* map (`Units.map ...`).

Consequently `σ • ·` is a group endomorphism of `𝕀 L`: it suffices to compare components, and at
each component the left hand side is `σ_*(x_{σ⁻¹ w} · y_{σ⁻¹ w}) = σ_*(x_{σ⁻¹ w}) · σ_*(y_{σ⁻¹ w})`
because `Units.map` is multiplicative, which is the right hand side.

Together with `NK.GlobalCFT.Galois.globalCFT_one_smul_idele` and
`NK.GlobalCFT.Galois.globalCFT_mul_smul_idele` this shows that the action makes `𝕀 L` into a
`Gal(L/K)`-module (the group ring `ℤ[Gal(L/K)]` acting by group endomorphisms), the starting
point of the Galois-theoretic description of the idèle class group.

## Main results

* `NK.GlobalCFT.Galois.globalCFT_smul_idele_mul`: `σ • (x * y) = σ • x * σ • y`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NumberField RestrictedProduct

namespace NK.GlobalCFT.Galois

/-- `Gal(L/K)` acts by group endomorphisms on the idèles: `σ • (x * y) = σ • x * σ • y`.
Indeed both sides are idèles, so it suffices to compare their components, and the component at
`w` of the left hand side is `σ_*(x_{σ⁻¹ w} · y_{σ⁻¹ w})`, which equals
`σ_*(x_{σ⁻¹ w}) · σ_*(y_{σ⁻¹ w})` because `σ_*` is a ring (hence multiplicative) equivalence
(`Units.map` of `(Place.localRingEquiv σ⁻¹ w).symm`), i.e. the component at `w` of the right
hand side. -/
theorem globalCFT_smul_idele_mul {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L) (x y : NK.GlobalCFT.Idele L) :
    σ • (x * y) = σ • x * σ • y := by
  -- Idèles are equal as soon as their components are equal.
  ext w
  -- Componentwise, this is the multiplicativity of `Units.map` of the (ring, hence
  -- multiplicative) equivalence `(Place.localRingEquiv σ⁻¹ w).symm`, together with the fact that
  -- multiplication in the restricted product `𝕀 L` is pointwise.
  simp [Idele.smul_apply, Idele.mul_apply]

end NK.GlobalCFT.Galois

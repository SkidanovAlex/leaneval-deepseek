import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A surjection between isomorphic finite free `ℤ`-modules of equal rank is injective

Let `M` and `N` be `ℤ`-modules each isomorphic to `ℤ^n` for the same `n`, and let
`f : M →ₗ[ℤ] N` be a surjective linear map.  Then `f` is injective.

This is the stably-finite / Hopfian property of finite free modules over `ℤ`.
Here it is deduced from Orzech's theorem for Noetherian modules
(`IsNoetherian.injective_of_surjective_of_injective`): a linear map `N →ₗ M` that is
injective and a linear map `N →ₗ M` that is surjective force the latter to be injective;
instantiating this with the composite of the two given linear equivalences as the injective
map, and with `f` (whose target is Noetherian, being a quotient of `ℤ^n`) as the surjective
map, yields the result.
-/

namespace Work.BridgeSquare

theorem injective_of_surjective_of_rank {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] {n : ℕ} (eM : M ≃ₗ[ℤ] (Fin n → ℤ)) (eN : N ≃ₗ[ℤ] (Fin n → ℤ))
    (f : M →ₗ[ℤ] N) (hf : Function.Surjective f) : Function.Injective f := by
  -- `N` is a finite module over the Noetherian ring `ℤ`, hence Noetherian.
  have hfin : Module.Finite ℤ N := Module.Finite.equiv eN.symm
  have hnoeth : IsNoetherian ℤ N := isNoetherian_of_isNoetherianRing_of_finite ℤ N
  -- `eN.symm ∘ eM : M →ₗ[ℤ] N` is injective; `f` is surjective; so `f` is injective.
  exact IsNoetherian.injective_of_surjective_of_injective
    ((eN.symm : (Fin n → ℤ) →ₗ[ℤ] N).comp (eM : M →ₗ[ℤ] (Fin n → ℤ)))
    f (by
      intro x y hxy
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hxy
      exact eM.injective (eN.symm.injective hxy)) hf

end Work.BridgeSquare

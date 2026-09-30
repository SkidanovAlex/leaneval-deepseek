import Mathlib
import Submission.Work.BridgeSquare.Data

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory

namespace Work.BridgeSquare

/-- **Singular chains are injective on injective maps.**
An injective continuous map `i : Y ⟶ X` induces an injective map on singular `k`-simplices (a
singular simplex is post-composed with `i`, which is injective), hence an injective map of the
free `ℤ`-modules of singular `k`-chains.

Formally: injectivity of `i` is monomorphy in `TopCat`; the singular chain complex (with
coefficients in `ℤ`) preserves monomorphisms; monomorphisms in a category of chain complexes over
`ModuleCat ℤ` are detected degreewise; and in `ModuleCat ℤ` monomorphisms are exactly the
injective linear maps. -/
theorem singChain_map_injective {Y X : TopCat} (i : Y ⟶ X) (hi : Function.Injective i) (k : ℕ) :
    Function.Injective (((Work.BridgeSquare.singCxFun).map i).f k).hom := by
  -- Injectivity of a continuous map is monomorphy in `TopCat`.
  have hmono : Mono i := (TopCat.mono_iff_injective i).mpr hi
  -- Monomorphy is detected by the underlying function of a homomorphism of `ℤ`-modules.
  rw [← ModuleCat.mono_iff_injective]
  -- `singCxFun` preserves monomorphisms, and monomorphy of a chain map is componentwise.
  infer_instance

end Work.BridgeSquare

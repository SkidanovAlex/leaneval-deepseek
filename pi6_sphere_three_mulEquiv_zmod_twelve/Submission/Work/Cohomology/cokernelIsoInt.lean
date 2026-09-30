import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cohomology

open CategoryTheory

/-- If `f : A ⟶ B` has image the kernel of a surjection `φ : B ⟶ ℤ`, then the cokernel of `f`
is `ℤ`.  This is the first isomorphism theorem for `ℤ`-modules, phrased categorically. -/
theorem cokernelIsoInt {A B : ModuleCat ℤ} (f : A ⟶ B) (φ : B ⟶ ModuleCat.of ℤ ℤ)
    (hsurj : Function.Surjective φ.hom) (hker : LinearMap.range f.hom = LinearMap.ker φ.hom) :
    Nonempty (CategoryTheory.Limits.cokernel f ≅ ModuleCat.of ℤ ℤ) := by
  refine ⟨?_⟩
  -- `cokernel f ≅ B ⧸ range f`
  refine (ModuleCat.cokernelIsoRangeQuotient f).trans ?_
  -- rewrite `range f` as `ker φ`
  refine ((Submodule.quotEquivOfEq (p := f.hom.range) (p' := LinearMap.ker φ.hom) hker).toModuleIso).trans ?_
  -- first isomorphism theorem for the surjection `φ`
  exact (LinearMap.quotKerEquivOfSurjective φ.hom hsurj).toModuleIso

end Work.Cohomology

import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Finiteness of homology of a binary biproduct of chain complexes

Let `C` and `D` be chain complexes of `ℤ`-modules.  If the `k`-th homology of `C`
and of `D` are both finite as `ℤ`-modules, then so is the `k`-th homology of the
binary biproduct `C ⊞ D`.

The point is that homology is an additive functor, hence preserves binary
biproducts: `(C ⊞ D).homology k ≅ C.homology k ⊞ D.homology k`.  Finiteness is
preserved by this isomorphism, and the biproduct in `ModuleCat ℤ` is (isomorphic
to) the cartesian product of the underlying modules, which is finite when both
factors are.
-/

open CategoryTheory Limits

namespace Work.ThomBordism

/-- Finiteness is preserved by the binary biproduct in `ModuleCat ℤ`. -/
private lemma moduleFinite_biprod (X Y : ModuleCat ℤ) (hX : Module.Finite ℤ X)
    (hY : Module.Finite ℤ Y) : Module.Finite ℤ (X ⊞ Y : ModuleCat ℤ) := by
  haveI := hX
  haveI := hY
  -- The biproduct of `ℤ`-modules is the product of the underlying modules.
  -- We work with the explicit product module structure `Prod.instModule`, which is
  -- the one used by `ModuleCat.biprodIsoProd` (over `ℤ` this differs definitionally
  -- from the instance coming from the abelian group structure).
  letI : Module ℤ (↥X × ↥Y) := Prod.instModule
  haveI : Module.Finite ℤ (↥X × ↥Y) := Module.Finite.prod
  exact Module.Finite.equiv (ModuleCat.biprodIsoProd X Y).symm.toLinearEquiv

/-- In a chain complex of `ℤ`-modules, homology of a binary biproduct in degree `k`
is finite whenever both summands have finite homology in degree `k`. -/
theorem moduleFiniteHomologyBiprod {C D : ChainComplex (ModuleCat ℤ) ℕ} (k : ℕ)
    (hC : Module.Finite ℤ (C.homology k)) (hD : Module.Finite ℤ (D.homology k)) :
    Module.Finite ℤ ((C ⊞ D).homology k) := by
  -- The `k`-th homology functor is additive, hence preserves binary biproducts.
  haveI : PreservesBinaryBiproducts
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  have e : (C ⊞ D).homology k ≅ (C.homology k ⊞ D.homology k : ModuleCat ℤ) :=
    Functor.mapBiprod
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k) C D
  haveI : Module.Finite ℤ (C.homology k ⊞ D.homology k : ModuleCat ℤ) :=
    moduleFinite_biprod (C.homology k) (D.homology k) hC hD
  exact Module.Finite.equiv e.symm.toLinearEquiv

end Work.ThomBordism

import Mathlib
import Submission.Work.Tower.Defs
import Submission.Work.Tower.Unramified.Basic
import Submission.Work.Tower.Unramified.Discriminant
import Submission.Work.Tower.FrattiniLayer.Basic
import Submission.Work.Tower.FrattiniLayer.isUnramifiedOver_of_algEquiv

/-!
# Transfer of the tower-cutting hypotheses along `F`-algebra isomorphisms

The maximal field of the tower-cutting argument is built as a compositum of the images of
"good" extensions under `F`-embeddings.  To read off the properties of an image from those of
the extension itself we record that unramifiedness, Galoisness and the `3`-group property are
invariant under `F`-algebra isomorphisms.
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work
namespace Tower
namespace TowerCut

variable {F L L' : Type*}

/-- Unramifiedness at every finite prime is invariant under `F`-algebra isomorphisms. -/
theorem isUnramifiedExtensionForallPrimes_of_algEquiv [Field F] [NumberField F] [Field L]
    [NumberField L] [Field L'] [NumberField L'] [Algebra F L] [Algebra F L']
    [FiniteDimensional F L] [FiniteDimensional F L'] (e : L ≃ₐ[F] L')
    (h : IsUnramifiedExtensionForallPrimes F L) : IsUnramifiedExtensionForallPrimes F L' :=
  (FrattiniLayer.isUnramifiedOver_iff_forallPrimes).mp
    (FrattiniLayer.isUnramifiedOver_of_algEquiv e
      ((FrattiniLayer.isUnramifiedOver_iff_forallPrimes).mpr h))

/-- The `3`-group property of the Galois group is invariant under `F`-algebra isomorphisms. -/
theorem isPGroup_gal_of_algEquiv [Field F] [Field L] [Field L'] [Algebra F L] [Algebra F L']
    (e : L ≃ₐ[F] L') (h : IsPGroup 3 (Gal(L/F))) : IsPGroup 3 (Gal(L'/F)) :=
  h.of_equiv (AlgEquiv.autCongr e)

/-- Galoisness is invariant under `F`-algebra isomorphisms. -/
theorem isGalois_of_algEquiv [Field F] [Field L] [Field L'] [Algebra F L] [Algebra F L']
    (e : L ≃ₐ[F] L') (h : IsGalois F L) : IsGalois F L' :=
  IsGalois.of_algEquiv e

/-- Finite-dimensionality is invariant under `F`-algebra isomorphisms. -/
theorem finiteDimensional_of_algEquiv [Field F] [Field L] [Field L'] [Algebra F L] [Algebra F L']
    (e : L ≃ₐ[F] L') [FiniteDimensional F L] : FiniteDimensional F L' :=
  Module.Finite.of_surjective (R := F) (M := L) (S := F) (σ := RingHom.id F)
    (e.toLinearMap) e.surjective

/-- The relative finrank is invariant under `F`-algebra isomorphisms. -/
theorem finrank_eq_of_algEquiv [Field F] [Field L] [Field L'] [Algebra F L] [Algebra F L']
    (e : L ≃ₐ[F] L') : Module.finrank F L = Module.finrank F L' :=
  (e : L ≃ₗ[F] L').finrank_eq

end TowerCut
end Tower
end Work

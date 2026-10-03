import Mathlib
import Submission.Work.ORReductions.API

/-!
# Coherence of `K[G]` is invariant under `ULift`

The monoid algebra `K[G]` and the monoid algebra `(ULift K)[ULift G]` are canonically
isomorphic rings: both directions just "lift" group elements and coefficients.  Concretely the
isomorphism sends `single g k` to `single (ULift.up g) (ULift.up k)`.  Since `Ring.Coherent`
(a notion of chase, defined in `ChallengeDeps`) is invariant under ring isomorphisms
(`Work.ORReductions.Coherent.coherent_of_ringEquiv`), the property transfers in both directions.

This is the `ULift` bookkeeping step of the assembly: it lets the main argument move between the
universes of the statement and those of the library on one-relator groups, freely.
-/

universe u v w

namespace Work.ORAssembly.Ulift

/-- The canonical ring equivalence `K[G] →+* (ULift K)[ULift G]`, defined as the composite of
the two "obvious" isomorphisms `K[G] ≃+* K[ULift G]` (`MonoidAlgebra.mapDomainRingEquiv`) and
`K[ULift G] ≃+* (ULift K)[ULift G]` (`MonoidAlgebra.mapRingEquiv`). -/
noncomputable def uliftMonoidAlgebraRingEquiv (K : Type v) (G : Type u) [Semiring K] [Monoid G] :
    MonoidAlgebra K G ≃+* MonoidAlgebra (ULift.{w} K) (ULift.{w} G) :=
  (MonoidAlgebra.mapDomainRingEquiv K (MulEquiv.ulift (α := G)).symm).trans
    (MonoidAlgebra.mapRingEquiv (ULift.{w} G) (ULift.ringEquiv (R := K)).symm)

/-- The ring equivalence `K[G] ≃+* (ULift K)[ULift G]` acts on basis elements by
`single g k ↦ single (ULift.up g) (ULift.up k)`. -/
@[simp] theorem uliftMonoidAlgebraRingEquiv_single {K : Type v} {G : Type u} [Semiring K]
    [Monoid G] (g : G) (k : K) :
    uliftMonoidAlgebraRingEquiv K G (MonoidAlgebra.single g k) =
      MonoidAlgebra.single (ULift.up g) (ULift.up k) := by
  simp [uliftMonoidAlgebraRingEquiv]; rfl

theorem ringCoherent_ulift (K : Type v) (G : Type u) [Semiring K] [Monoid G] :
    Ring.Coherent (MonoidAlgebra K G) ↔
      Ring.Coherent (MonoidAlgebra (ULift.{w} K) (ULift.{w} G)) :=
  ⟨fun h => Ring.Coherent.of_ringEquiv (uliftMonoidAlgebraRingEquiv K G) h,
   fun h => Ring.Coherent.of_ringEquiv (uliftMonoidAlgebraRingEquiv K G).symm h⟩

end Work.ORAssembly.Ulift

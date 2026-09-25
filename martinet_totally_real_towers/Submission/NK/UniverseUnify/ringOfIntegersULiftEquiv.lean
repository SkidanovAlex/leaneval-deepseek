import Mathlib
import Submission.NK.UniverseUnify.Defs

/-!
# The ring of integers is invariant under `ULift`

The ring of integers `NumberField.RingOfIntegers K = integralClosure ℤ K` of a number field depends
only on the isomorphism class of `K`, and `ULift.ringEquiv : ULift.{w} K ≃+* K` is an isomorphism of
`ℤ`-algebras.  Mapping the integral closure along an algebra equivalence gives the integral closure
(`AlgEquiv.mapIntegralClosure`), so the two rings of integers are isomorphic.

This is the (elementary) universe transport for `𝓞`, needed whenever a statement about number fields
is proved in one universe and applied in another.
-/

namespace NK.UniverseUnify

universe u w

/-- **The ring of integers is invariant under `ULift`.**

`ULift.ringEquiv : ULift K ≃+* K` is (canonically) an isomorphism of `ℤ`-algebras
(`RingEquiv.toIntAlgEquiv`), and an algebra isomorphism restricts to an isomorphism of the integral
closures (`AlgEquiv.mapIntegralClosure`).  Since `NumberField.RingOfIntegers K` is
`integralClosure ℤ K`, this is an isomorphism `𝓞 (ULift K) ≃+* 𝓞 K`. -/
theorem ringOfIntegersULiftEquiv (K : Type u) [Field K] [NumberField K] :
    Nonempty (NumberField.RingOfIntegers (ULift.{w} K) ≃+* NumberField.RingOfIntegers K) :=
  ⟨((ULift.ringEquiv : ULift.{w} K ≃+* K).toIntAlgEquiv).mapIntegralClosure.toRingEquiv⟩

end NK.UniverseUnify

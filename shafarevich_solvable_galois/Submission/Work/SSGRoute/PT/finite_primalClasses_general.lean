import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.PT.finite_H1loc
import Submission.Work.SSGRoute.PT.pt_counting_assembly
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

/-- **The primal local class space is finite, under the geometric hypotheses on `S` and `C`.**
This is the form in which the finiteness is needed downstream: the places of `S` are finite
places (`SSGRoute.IsFinPlace`) and the elements of `C` are involutions (`c ^ 2 = 1`), the two
cases in which the local `H¹` at the corresponding decomposition group is known to be finite.

* at a finite place `A ∈ S`, finiteness is `Work.SSGRoute.PT.finite_H1loc` (local Tate duality
  for a non-archimedean place);
* at an involution `c ∈ C`, finiteness is `Work.SSGRoute.PT.finite_H1loc_zpowers` (the group
  `⟨c⟩` has order `≤ 2`).

The product over the two finite index sets is then finite by
`Work.SSGRoute.PT.finite_primalClasses`. -/
theorem finite_primalClasses_general (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (X : Type) [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction (K ≃ₐ[k] K) X] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) X] [Finite X]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (C : Finset (Ω ≃ₐ[k] Ω)) (hCinv : ∀ c ∈ C, c ^ 2 = 1) :
    Finite (Work.SSGRoute.PT.primalClasses p k Ω K X S C) :=
  finite_primalClasses p k Ω K X S C
    (fun A hA => finite_H1loc p k Ω K X A (hSfin A hA))
    (fun c hc => finite_H1loc_zpowers p k Ω K X c (hCinv c hc))

end Work.SSGRoute.PT

import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZPlace
import Submission.Work.SSGRoute.inertiaSub_image_eq_levelInertia
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute.ZDataTwo

/-- **Unramifiedness in the `IsRamifiedIn` spelling gives ramification index one at the level
prime.** `IsRamifiedIn k L A` says that some inertia element of the place `A` fails to fix `L`
pointwise.  Consequently `Work.SSGRoute.inertiaSub k Ω A ≤ L.fixingSubgroup = ker (res k L)`, so
its image under the restriction is trivial.  By `Work.SSGRoute.inertiaSub_image_eq_levelInertia`
that image is `Ideal.inertia (↥L ≃ₐ[k] ↥L) (levelPrime k Ω A hA L).asIdeal`, and
`Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one` converts
triviality of that inertia into `ramificationIdx = 1`. -/
theorem ramificationIdx_levelPrime_eq_one_of_not_isRamifiedIn
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hunr : ¬ SSGRoute.IsRamifiedIn k L A) :
    (Work.SSGRoute.levelPrime k Ω A hA L).asIdeal.ramificationIdx
      (NumberField.RingOfIntegers k) = 1 := by
  classical
  haveI hNumL : NumberField ↥L :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField L
  haveI hNormL : Normal k ↥L := inferInstance
  -- The inertia subgroup of the place is contained in the kernel of the restriction to `L`:
  -- an inertia element fixing `L` pointwise is exactly what `¬ IsRamifiedIn` forbids.
  have hker : Work.SSGRoute.inertiaSub k Ω A ≤ (AlgEquiv.restrictNormalHom L).ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker]
    rw [show AlgEquiv.restrictNormalHom L σ = σ.restrictNormal ↥L from rfl,
      AlgEquiv.restrictNormal_eq_one_iff]
    intro x hx
    by_contra hne
    exact hunr ⟨σ, (Work.SSGRoute.mem_inertiaSub k Ω A σ).mp hσ,
      fun hmem => hne ((IntermediateField.mem_fixingSubgroup_iff L σ).mp hmem x hx)⟩
  -- Hence the level inertia is trivial, since it is the image of the place inertia.
  have hbot : Ideal.inertia (↥L ≃ₐ[k] ↥L)
      (Work.SSGRoute.levelPrime k Ω A hA L).asIdeal = ⊥ := by
    have hlev : Work.SSGRoute.levelInertiaOf k Ω A hA L = ⊥ := by
      rw [← Work.SSGRoute.inertiaSub_image_eq_levelInertia k Ω A hA L,
        Subgroup.map_eq_bot_iff]
      exact hker
    simpa only [Work.SSGRoute.levelInertiaOf, Work.SSGRoute.levelPrimeOf] using hlev
  -- And a trivial inertia subgroup means ramification index one.
  haveI hPprime : (Work.SSGRoute.levelPrime k Ω A hA L).asIdeal.IsPrime :=
    (Work.SSGRoute.levelPrime k Ω A hA L).isPrime
  exact (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
    ((Work.SSGRoute.levelPrime k Ω A hA L).asIdeal.under (NumberField.RingOfIntegers k))
    (Work.SSGRoute.levelPrime k Ω A hA L).asIdeal).mp hbot

end Work.SSGRoute.ZDataTwo

import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.inertiaAtLevelDefs
import Submission.Work.SSGRoute.InertiaDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Vocabulary for the level-theoretic proof of
`Work.SSGRoute.inf_inertia_closure_eq_bot`

For a number field `k`, an algebraic closure `Ω`, a finite place `A` of `Ω` and a finite normal
level `M ⊆ Ω` (a number field, `Normal k M`), write `P := levelPrimeAt k Ω A hA M` for the prime
of `𝓞 M` below `A`.  This file fixes the names

* `levelPrimeAt k Ω A hA M` — the prime of `𝓞 M` below `A` (`Work.SSGRoute.levelPrime`);
* `levelDecompAt k Ω A hA M` — its decomposition group `≤ Gal(M/k)`, the stabiliser of
  `P.asIdeal`;
* `levelInertiaAt k Ω A hA M` — its inertia subgroup `≤ Gal(M/k)`;
* `levelInertiaInDecompAt k Ω A hA M` — the inertia, as a subgroup of the decomposition group
  (`Ideal.inertia (levelDecompAt …) P.asIdeal`).

The intended use is that the restriction `AlgEquiv.restrictNormalHom M` maps the decomposition
group `SSGRoute.decomp k A` onto `levelDecompAt k Ω A hA M` and carries `SSGRoute.inertiaSub k Ω A`
into `levelInertiaAt k Ω A hA M`, so that it induces the level quotient
`D_A ⧸ (D_A ⊓ ⋯) ≅ levelDecompAt ⧸ levelInertiaInDecompAt`, whose order is the inertia degree
`P.asIdeal.inertiaDeg (𝓞 k)`.
-/

namespace Work.SSGRoute

open scoped Pointwise NumberField
open _root_.SSGRoute

variable (k : Type) [Field k] [NumberField k] (Ω : Type) [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

/-- **The prime of the finite level `M` below the finite place `A`.** -/
noncomputable abbrev levelPrimeAt (A : ValuationSubring Ω) (hA : IsFinPlace k A)
    (M : IntermediateField k Ω) [NumberField ↥M] : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥M) :=
  levelPrime k Ω A hA M

/-- **The decomposition group of the level prime, inside `Gal(M/k)`** (the stabiliser of the
prime ideal `P.asIdeal`). -/
noncomputable abbrev levelDecompAt (A : ValuationSubring Ω) (hA : IsFinPlace k A)
    (M : IntermediateField k Ω) [NumberField ↥M] : Subgroup (↥M ≃ₐ[k] ↥M) :=
  MulAction.stabilizer (↥M ≃ₐ[k] ↥M) (levelPrime k Ω A hA M).asIdeal

/-- **The inertia subgroup of the level prime, inside `Gal(M/k)`.** -/
noncomputable abbrev levelInertiaAt (A : ValuationSubring Ω) (hA : IsFinPlace k A)
    (M : IntermediateField k Ω) [NumberField ↥M] : Subgroup (↥M ≃ₐ[k] ↥M) :=
  Ideal.inertia (↥M ≃ₐ[k] ↥M) (levelPrime k Ω A hA M).asIdeal

/-- **The inertia subgroup of the level prime, as a subgroup of the level decomposition group.** -/
noncomputable abbrev levelInertiaInDecompAt (A : ValuationSubring Ω) (hA : IsFinPlace k A)
    (M : IntermediateField k Ω) [NumberField ↥M] : Subgroup (levelDecompAt k Ω A hA M) :=
  Ideal.inertia (levelDecompAt k Ω A hA M) (levelPrime k Ω A hA M).asIdeal

/-- The two descriptions of the level inertia inside the decomposition group agree:
`levelInertiaInDecompAt` is `(levelInertiaAt …).subgroupOf (levelDecompAt …)`. -/
lemma levelInertiaInDecompAt_eq (A : ValuationSubring Ω) (hA : IsFinPlace k A)
    (M : IntermediateField k Ω) [NumberField ↥M] :
    levelInertiaInDecompAt k Ω A hA M =
      (levelInertiaAt k Ω A hA M).subgroupOf (levelDecompAt k Ω A hA M) := by
  rw [levelInertiaInDecompAt, levelInertiaAt, levelDecompAt,
    AddSubgroup.subgroupOf_inertia]

end Work.SSGRoute

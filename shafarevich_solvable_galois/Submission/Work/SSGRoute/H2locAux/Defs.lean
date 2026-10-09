import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.inertiaAtLevelDefs
import Submission.NK.LocalTame.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Vocabulary for the vanishing of the second local cohomology of the inertia subgroup

This module collects the vocabulary in which the lemmas feeding
`Work.SSGRoute.H2loc_inertia_subsingleton` are stated.  Nothing here is proved.

* `Work.SSGRoute.IsProPrimeToP p G` — every normal finite-index subgroup of `G` has index prime
  to `p` (the finite-quotient formulation of "`G` is pro-prime-to-`p`");
* `Work.SSGRoute.IsProCyclicGrp G` — every finite quotient of `G` is cyclic;
* `Work.SSGRoute.levelPrimeOf` — the prime of `𝓞 M` below a place `A` of `Ω`, for a finite level
  `M`;
* `Work.SSGRoute.levelInertiaOf` — the inertia subgroup of `Gal(M/k)` at that prime ("the level
  inertia").
-/

open scoped Pointwise NumberField

namespace Work.SSGRoute

open _root_.SSGRoute

/-- **`G` is pro-prime-to-`p`**: every normal subgroup of finite index has index coprime to `p`.
(Re-export of `NK.LocalTame.IsProPrimeToP` in this namespace.) -/
abbrev IsProPrimeToP (p : ℕ) (G : Type*) [Group G] : Prop := NK.LocalTame.IsProPrimeToP p G

/-- **`G` is pro-cyclic**: every finite quotient of `G` is a cyclic group.  (Re-export of
`NK.LocalTame.IsProCyclic` in this namespace.) -/
abbrev IsProCyclicGrp (G : Type*) [Group G] : Prop := NK.LocalTame.IsProCyclic G

/-- The prime of `𝓞 M` below the place `A` of `Ω`. -/
noncomputable abbrev levelPrimeOf (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] [NumberField ↥M] :
    IsDedekindDomain.HeightOneSpectrum (𝓞 ↥M) :=
  levelPrime k Ω A hA M

/-- The **level inertia**: the inertia subgroup of `Gal(M/k)` at the prime of `𝓞 M` below `A`,
i.e. the elements acting trivially on the residue field of that prime. -/
noncomputable abbrev levelInertiaOf (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] [NumberField ↥M] :
    Subgroup (↥M ≃ₐ[k] ↥M) :=
  Ideal.inertia (↥M ≃ₐ[k] ↥M) (levelPrimeOf k Ω A hA M).asIdeal

end Work.SSGRoute

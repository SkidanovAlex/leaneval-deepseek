import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.ResidueFrob.exists_inertia_of_isTrivialOnResidueAtLevel
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-inertia vocabulary of `Work.SSGRoute.decomp_mod_inertia_cyclic`

Definitions only, so that the lemmas delegated for
`Work.SSGRoute.decomp_mod_inertia_cyclic` can be *stated* without mentioning the
`Submission.NK.*` vocabulary directly (the modules of `Submission/Work/` cannot depend on
`Submission/NK/` through the delegation interface, but they may use the definitions below).

* `Work.SSGRoute.levelPrime k Ω B hB L` — the prime of `𝓞 L` below the place `B`, for a finite
  normal level `L` (the `NK.Reconstruct.primeOfLevel` of the place below `B`, as a Mathlib
  `HeightOneSpectrum`);
* `Work.SSGRoute.IsTrivialAtLevel k Ω B hB L g` — `g` acts trivially on the residue field of `L`
  at the prime below `B` (the `NK.FrobeniusBridge.IsTrivialOnResidueAtLevel` of `⟨B, hB⟩`).
-/

open scoped Pointwise NumberField

attribute [instance] ValuationSubring.pointwiseMulAction
attribute [instance] Ideal.pointwiseDistribMulAction
attribute [instance] Ideal.pointwiseMulSemiringAction

namespace Work.SSGRoute

/-- **The prime of `𝓞 L` below the place `B`**: for a finite normal level `L` of the separable
closure `Ω` of the number field `k` and a place `B` of `Ω` over a finite prime of `k`. -/
noncomputable abbrev levelPrime (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (B : ValuationSubring Ω) (hB : B.comap (algebraMap k Ω) ≠ ⊤)
    (L : IntermediateField k Ω) [NumberField ↥L] : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥L) :=
  NK.Reconstruct.primeOfLevel B L (NK.Reconstruct.comap_level_ne_top hB L)

/-- **`g` acts trivially on the residue field of the finite normal level `L`** at the prime of
`𝓞 L` below the place `B`: the unfolded form of `NK.FrobeniusBridge.IsTrivialOnResidueAtLevel`
for the place `⟨B, hB⟩`. -/
abbrev IsTrivialAtLevel (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (B : ValuationSubring Ω) (hB : B.comap (algebraMap k Ω) ≠ ⊤)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [Normal k L] [NumberField ↥L]
    (g : Ω ≃ₐ[k] Ω) : Prop :=
  NK.FrobeniusBridge.IsTrivialOnResidueAtLevel ⟨B, hB⟩ L g

end Work.SSGRoute

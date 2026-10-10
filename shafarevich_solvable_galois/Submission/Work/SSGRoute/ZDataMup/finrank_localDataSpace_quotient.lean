import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZDataMup.finite_localDataSpace_quotient
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The dimension of the quotient `localDataSpace K T ⧸ localVanish K T`

The local-data space `localDataSpace K T` is the product, over the places `A ∈ T`, of the spaces
`localCocycle K H_A` of locally constant `1`-cocycles on the level-`K` local groups
`H_A = decomp k A ⊓ G_K` (`localDataSpace_eq_pi`).  The submodule `localVanish K T` consists of the
tuples all of whose components vanish on the corresponding local group.

The target of this file computes the `𝔽_p`-dimension of the quotient:

`finrank (localDataSpace K T ⧸ localVanish K T) = ∑_{A ∈ T} finrank (lcCocycleImage K H_A)`,

where `lcCocycleImage K H_A ≤ (↥H_A → ZMod p)` is the image of `localCocycle K H_A` under the
restriction of functions from `G_k` to `H_A`.  The dimension count is *exact*, not merely finite: the
restriction map `phi T` of `ZDataMup/finite_localDataSpace_quotient` has kernel `localVanish K T`
(`ker_phi`) and is **surjective** (`surjective_phi`), since each locally constant cocycle on `H_A`
extends by `0` to a cocycle on `G_k` (the elements of `lcCocycleImage` are by definition restrictions
of cocycles on `G_k`).  Hence the quotient is linearly isomorphic to the full product
`∏_{A ∈ T} lcCocycleImage K H_A`, whose dimension is the sum of the dimensions of its factors
(`Module.finrank_pi_fintype`).

## Added lemmas

* `surjective_phi` -- the restriction map `phi T` is onto;
* `finrank_localDataSpace_quotient` -- the dimension formula.
-/

open scoped Pointwise

set_option linter.style.haveILetI false

namespace Work.SSGRoute.ZDataMup

open _root_.SSGRoute

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-- **The restriction map `phi T` is surjective.**  By definition of `lcCocycleImage`, a locally
constant cocycle on the level-`K` local group `H_A = decomp k A ⊓ G_K` is the restriction to `H_A`
of a locally constant cocycle on `G_k`; the tuple of these extensions is an element of
`localDataSpace K T` mapping to the given family.  Consequently
`localDataSpace K T ⧸ phi.ker` is the *full* product of the spaces `lcCocycleImage K H_A`. -/
theorem surjective_phi (T : Finset (ValuationSubring Ω)) :
    Function.Surjective (phi (p := p) (K := K) T) := by
  intro x
  choose b hb hbx using fun A => Submodule.mem_map.mp (x A).2
  refine ⟨⟨fun A => b A, fun A => hb A⟩, ?_⟩
  funext A
  exact Subtype.ext (hbx A)

/-- **The dimension of the quotient `localDataSpace K T ⧸ localVanish K T`.**  Since `phi T` has
kernel `localVanish K T` and is surjective, the quotient is linearly isomorphic to the product
`∏_{A ∈ T} lcCocycleImage K H_A`; the dimension of a finite product is the sum of the dimensions of
its factors. -/
theorem finrank_localDataSpace_quotient {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] (T : Finset (ValuationSubring Ω))
    (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A) :
    Module.finrank (ZMod p)
        (↥(Work.SSGRoute.ZDataMup.localDataSpace (p := p) K T) ⧸
          Work.SSGRoute.ZDataMup.localVanish (p := p) K T) =
      ∑ A : {A : ValuationSubring Ω // A ∈ T},
        Module.finrank (ZMod p)
          ↥(Work.SSGRoute.ZDataMup.lcCocycleImage (p := p) K
            (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup)) := by
  classical
  haveI hfinite : ∀ A : {A : ValuationSubring Ω // A ∈ T},
      Finite ↥(lcCocycleImage (p := p) K (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup)) :=
    fun A => finite_lcCocycleImage (p := p) (K := K) (hA := hTfin A.1 A.2)
  haveI hmodfin : ∀ A : {A : ValuationSubring Ω // A ∈ T},
      Module.Finite (ZMod p)
        ↥(lcCocycleImage (p := p) K (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup)) :=
    fun _ => Module.Finite.of_finite
  haveI hfree : ∀ A : {A : ValuationSubring Ω // A ∈ T},
      Module.Free (ZMod p)
        ↥(lcCocycleImage (p := p) K (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup)) :=
    fun _ => Module.Free.of_divisionRing (ZMod p) _
  have e : (↥(localDataSpace (p := p) K T) ⧸ localVanish (p := p) K T) ≃ₗ[ZMod p]
      (∀ A : {A : ValuationSubring Ω // A ∈ T},
        ↥(lcCocycleImage (p := p) K (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup))) :=
    (Submodule.quotEquivOfEq (localVanish (p := p) K T) (phi (p := p) (K := K) T).ker
      (ker_phi (p := p) (K := K) T).symm).trans
      ((LinearMap.quotKerEquivRange (phi (p := p) (K := K) T)).trans
        (LinearEquiv.ofTop _
          (LinearMap.range_eq_top.mpr (surjective_phi (p := p) (K := K) T))))
  rw [e.finrank_eq, Module.finrank_pi_fintype]

end Work.SSGRoute.ZDataMup

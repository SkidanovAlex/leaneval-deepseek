import Mathlib
import Submission.Work.SSGRoute.ZDataMup.localGlobalProductFormula_cyclic
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.kernelLeId
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The product form of Hilbert reciprocity for cyclic extensions

`Work.SSGRoute.ZDataMup.ArtinReciprocity.productFormula_cyclic` is the *product form* of Hilbert
reciprocity for a finite cyclic extension `L / K` of number fields (Milne, *CFT*, VII.8.1(a)):
there is a monoid homomorphism `Φ : 𝕀_K →* Gal(L/K)` which kills the principal idèles `Kˣ`, kills
the idèles that are norms from `L`, and sends the prime idèle at every unramified prime `Q` to the
Frobenius element `Frob_Q`.

Equivalently it says that the product `∏_v λ_v` of the local Artin maps vanishes on `Kˣ`
(`∑_v inv_v = 0`); the classical proof is Milne, *CFT*, Ch. VII §8.

## How it is proved here

The assembly `Work.SSGRoute.ZDataMup.exists_artinMap_productFormula_cyclic_of_crux` builds the map
from

* Lang's conductor theorem for an **ideal** modulus (Lang, *Algebraic Number Theory*, X §2 Thm 2;
  Childress, *Class Field Theory*, Prop. 2.2): for an admissible ideal modulus `𝔪` containing all
  the primes ramified in `L/K`, every fractional ideal `A` of `K` coprime to `𝔪` whose Artin symbol
  is trivial lies in `P(𝔪)·𝔑(𝔪)` —

this is exactly the statement of
`Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.kernelLeId`, which is proved (by the transfer
argument of Lang, *Algebraic Number Theory*, X §2, transported from the natural-number-modulus
version `NK.NUV2.ARL.SC.kernelLeOfAuxFieldSC`) in this lane.

Feeding that crux to `exists_artinMap_productFormula_cyclic_of_crux` passes through
`hprinc_idealModulus_ramifiedSupport` (the ideal modulus supported exactly on the ramified primes,
together with its conductor drop) and `Cycle.localGlobalMap_productFormula_of_cycleDrop`, which
builds the idèlic Artin map of the congruence subgroup of that ideal modulus.  Its three clauses
"kills `Kˣ`", "kills the idèlic norms" and the Frobenius normalisation at every unramified prime
are precisely the three clauses of the target.

The one extra clause `Function.Surjective Φ` produced by the assembly is not asserted in the
target and is simply dropped.
-/

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity

/-- **The product form of Hilbert reciprocity for cyclic extensions** (Milne, *CFT*, VII.8.1(a)).

For a finite cyclic extension `L/K` of number fields there is a homomorphism
`Φ : 𝕀_K →* Gal(L/K)` out of the idèle group of `K` which

* kills every principal idèle `(a)`, `a : Kˣ`;
* kills every idèle that is the norm of an idèle of `L`;
* sends the prime idèle at every unramified prime `Q` of `K` to the Frobenius element `Frob_Q`. -/
theorem productFormula_cyclic
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    ∃ Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L),
      (∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1) ∧
      (∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1) ∧
      (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) := by
  -- the assembly, with Lang's conductor theorem for an ideal modulus supplied by the transfer lane
  obtain ⟨Φ, hprincipal, hnorm, -, hfrob⟩ :=
    Work.SSGRoute.ZDataMup.exists_artinMap_productFormula_cyclic_of_crux (K := K) (L := L)
      (fun hcomm 𝔪 h𝔪 hadm hram =>
        Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.kernelLeId hcomm 𝔪 h𝔪 hadm hram)
  exact ⟨Φ, hprincipal, hnorm, hfrob⟩

end Work.SSGRoute.ZDataMup.ArtinReciprocity

import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZConstruction.kummerCharLift
import Submission.Work.SSGRoute.ZConstruction.quotientKerLocalPowClassEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-`K` local Kummer map on the local `p`-th power class group

Transporting the injective descent `kummerCharLift` (`Kˣ ⧸ ker ρ →* ↥(lcHoms p ↥(decomp (k := ↥K) A))`)
across the identification `quotientKerLocalPowClassEquiv : Kˣ ⧸ ker ρ ≃* κˣ ⧸ (κˣ)^p` gives a
monoid homomorphism

  `localKummerHom : κˣ ⧸ (κˣ)^p →* ↥(lcHoms p ↥(decomp (k := ↥K) A))`,

which is again **injective**.  With the equal finite cardinalities of
`natCard_lcHoms_levelK_localGroup` that makes it bijective -- the level-`K` local Kummer isomorphism
`κˣ ⧸ (κˣ)^p ≅ H1loc p k Ω K (ZMod p) (decomp k A ⊓ K.fixingSubgroup)` (after the crossing through
`Work.SSGRoute.PTembedding.z1_triv_card_eq_lcHoms`).
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  {ζ : ↥K} {hζ : IsPrimitiveRoot ζ p} {A : ValuationSubring Ω}

/-- **The level-`K` local Kummer map**, on the local `p`-th power class group. -/
noncomputable def localKummerHom (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) :
    ((𝔭.adicCompletion ↥K)ˣ ⧸
        ((powMonoidHom p : (𝔭.adicCompletion ↥K)ˣ →* (𝔭.adicCompletion ↥K)ˣ).range)) →*
      ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) :=
  (kummerCharLift (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA 𝔭 h𝔭).comp
    ((quotientKerLocalPowClassEquiv (p := p) (K := K) 𝔭).symm : _ →* _)

/-- **The level-`K` local Kummer map is injective.** -/
theorem localKummerHom_injective (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) :
    Function.Injective (localKummerHom (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
      (A := A) hA 𝔭 h𝔭) :=
  (kummerCharLift_injective (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
    (A := A) hA 𝔭 h𝔭).comp (quotientKerLocalPowClassEquiv (p := p) (K := K) 𝔭).symm.injective

end Work.SSGRoute.ZConstruction

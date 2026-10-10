import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZConstruction.quotientKer_localPowClass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Kˣ ⧸ ker ρ ≃* κˣ ⧸ (κˣ)^p`

The first isomorphism theorem for the local reduction `ρ = NK.UchidaKummer.localPowClass ↥K p 𝔭`,
with the range identified with the whole `p`-th power class group of the completion via
`localPowClass_range_eq_top`.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  {ζ : ↥K} {hζ : IsPrimitiveRoot ζ p} {A : ValuationSubring Ω}

/-- **The local `p`-th power class group of the completion is `Kˣ ⧸ ker ρ`.** -/
noncomputable def quotientKerLocalPowClassEquiv
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :
    (Kˣ ⧸ MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p 𝔭)) ≃*
      ((𝔭.adicCompletion ↥K)ˣ ⧸
        ((powMonoidHom p : (𝔭.adicCompletion ↥K)ˣ →* (𝔭.adicCompletion ↥K)ˣ).range)) := by
  refine (QuotientGroup.quotientKerEquivRange
    (NK.UchidaKummer.localPowClass ↥K p 𝔭)).trans ?_
  rw [localPowClass_range_eq_top (p := p) (K := K) 𝔭]
  exact Subgroup.topEquiv

end Work.SSGRoute.ZConstruction

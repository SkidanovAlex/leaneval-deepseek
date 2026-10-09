import Mathlib
import Submission.Work.SSGRoute.ZConstruction.localPowClass_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The first isomorphism theorem for the local reduction `ρ : Kˣ →* κˣ ⧸ (κˣ)^p`

`Work.SSGRoute.ZConstruction.localPowClass_surjective` says that the local reduction
`ρ = NK.UchidaKummer.localPowClass ↥K p 𝔭` is onto; the first isomorphism theorem then identifies
`Kˣ ⧸ ker ρ` with the range of `ρ`, and (`localPowClass_range_eq_top`) that range is everything:

  `Kˣ ⧸ ker ρ ≃* κˣ ⧸ (κˣ)^p`.

This is the identification across which the injective descent `kummerCharLift`
(`Kˣ ⧸ ker ρ →* ↥(lcHoms p ↥(decomp (k := ↥K) A))`, kernel `ker ρ ⧸ ker ρ`) becomes a monomorphism
`κˣ ⧸ (κˣ)^p →* ↥(lcHoms p ↥(decomp A))`, which -- with the equal finite cardinalities of
`natCard_lcHoms_levelK_localGroup` -- is the level-`K` local Kummer isomorphism.

For Lean: the range-form isomorphism is stated as
`quotientKerLocalPowClassEquivRange`; to land on the class group itself, compose with
`Subgroup.topEquiv` after rewriting by `localPowClass_range_eq_top` (or use
`MulEquiv.subgroupCongr` at that equation).
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  {ζ : ↥K} {hζ : IsPrimitiveRoot ζ p} {A : ValuationSubring Ω}

/-- **The range of the local reduction is everything.** -/
theorem localPowClass_range_eq_top
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :
    MonoidHom.range (NK.UchidaKummer.localPowClass ↥K p 𝔭) = ⊤ :=
  MonoidHom.range_eq_top.mpr (localPowClass_surjective (p := p) (K := K) 𝔭)

/-- **The first isomorphism theorem for the local reduction.** -/
noncomputable def quotientKerLocalPowClassEquivRange
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :
    (Kˣ ⧸ MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p 𝔭)) ≃*
      MonoidHom.range (NK.UchidaKummer.localPowClass ↥K p 𝔭) :=
  QuotientGroup.quotientKerEquivRange _

end Work.SSGRoute.ZConstruction

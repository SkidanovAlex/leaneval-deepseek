import Mathlib
import Submission.Work.SSGRoute.ZConstruction.localPowClass_ker_le_kummerChar_ker
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The descent of the Kummer map to the kernel of the local reduction

`QuotientGroup.lift` at the kernel of `ρ = NK.UchidaKummer.localPowClass ↥K p 𝔭` gives the induced
map `kummerCharLift : Kˣ ⧸ ker ρ →* ↥(lcHoms p ↥(decomp (k := ↥K) A))`, with the computation rule
`kummerCharLift (mk β) = χ_β`.

Injectivity of `kummerCharLift` (the next step, deliberately not carried here half-proved) is
elementwise: take `a = mk x`, `b = mk y` (`QuotientGroup.mk'_surjective`), rewrite both sides by
`kummerCharLift_mk` so the hypothesis becomes `Φ x = Φ y`, derive `x * y⁻¹ ∈ MonoidHom.ker Φ` from
it (`MonoidHom.mem_ker`, `map_mul`, `map_inv`, the hypothesis, `mul_inv_cancel`), cross to
`MonoidHom.ker ρ` by `kummerChar_ker_le_localPowClass_ker`, and conclude `mk x = mk y` through
`mul_inv_eq_one` backwards together with `QuotientGroup.ker_mk'`.  Note that the
`MonoidHom.ker_eq_bot_iff` route does not match the goal `Function.Injective (kummerCharLift …)`, so
the elementwise form is the one to use.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  {ζ : ↥K} {hζ : IsPrimitiveRoot ζ p} {A : ValuationSubring Ω}

/-- **The Kummer map descended to the quotient by the kernel of the local reduction.** -/
noncomputable def kummerCharLift (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) :
    (Kˣ ⧸ MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p 𝔭)) →*
      ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) :=
  QuotientGroup.lift (MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p 𝔭))
    (kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA)
    (localPowClass_ker_le_kummerChar_ker (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ)
      (hζ := hζ) (A := A) hA 𝔭 h𝔭)

/-- The computation rule: `kummerCharLift (mk β) = χ_β`. -/
theorem kummerCharLift_mk (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) (β : Kˣ) :
    kummerCharLift (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA 𝔭 h𝔭
        (QuotientGroup.mk' (MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p 𝔭)) β)
      = kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
          (A := A) hA β :=
  QuotientGroup.lift_mk' _ _ _

/-- **The descended Kummer map is injective.** -/
theorem kummerCharLift_injective (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) :
    Function.Injective (kummerCharLift (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ)
      (hζ := hζ) (A := A) hA 𝔭 h𝔭) := by
  intro a b hab
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p 𝔭)) a
  obtain ⟨y, rfl⟩ :=
    QuotientGroup.mk'_surjective (MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p 𝔭)) b
  -- the descended equality is the equality of Kummer characters
  have hab' : kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
        (A := A) hA x
      = kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
        (A := A) hA y := by
    simpa only [kummerCharLift_mk] using hab
  -- hence `x * y⁻¹` has trivial Kummer character, i.e. lies in `ker Φ`
  have h1 : x * y⁻¹ ∈ MonoidHom.ker (kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K)
      (ζ := ζ) (hζ := hζ) (A := A) hA) := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab', mul_inv_cancel]
  -- and therefore in `ker ρ`, by the reverse kernel inclusion
  have h2 : x * y⁻¹ ∈ MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p 𝔭) :=
    kummerChar_ker_le_localPowClass_ker (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ)
      (hζ := hζ) (A := A) hA 𝔭 h𝔭 h1
  -- so the two cosets agree
  have h3 : (QuotientGroup.mk' (MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p 𝔭)))
      (x * y⁻¹) = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact h2
  have h4 : (QuotientGroup.mk' (MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p 𝔭))) x
      * ((QuotientGroup.mk' (MonoidHom.ker (NK.UchidaKummer.localPowClass ↥K p 𝔭))) y)⁻¹ = 1 := by
    rw [← map_inv, ← map_mul]
    exact h3
  exact mul_inv_eq_one.mp h4

end Work.SSGRoute.ZConstruction

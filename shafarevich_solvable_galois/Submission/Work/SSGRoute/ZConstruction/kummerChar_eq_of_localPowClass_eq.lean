import Mathlib
import Submission.Work.SSGRoute.ZConstruction.kummerCharMonoidHom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer map is well defined on local `p`-th power classes

`β ↦ χ_β` (`kummerCharMonoidHom`) kills exactly the local `p`-th powers
(`kummerCharMonoidHom_eq_one_iff`), and `β ↦ [β]` (`NK.UchidaKummer.localPowClass` into
`κˣ ⧸ (κˣ)^p`) is the reduction modulo them.  Hence the Kummer map **descends** to the local
`p`-th power classes: two global units with the same local `p`-th power class have the same Kummer
character.

This is the hypothesis of `QuotientGroup.lift` when the induced map
`κˣ ⧸ (κˣ)^p →* ↥(lcHoms p ↥(decomp (k := ↥K) A))` is built, and — because the reduction is
surjective (`exists_globalUnit_mul_pow_eq_of_local`) — it is simultaneously the *injectivity* of the
induced map.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  {ζ : ↥K} {hζ : IsPrimitiveRoot ζ p} {A : ValuationSubring Ω}

/-- **The Kummer map is constant on local `p`-th power classes.** -/
theorem kummerChar_eq_of_localPowClass_eq (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (β β' : Kˣ)
    (h : NK.UchidaKummer.localPowClass ↥K p 𝔭 β = NK.UchidaKummer.localPowClass ↥K p 𝔭 β') :
    kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA β
      = kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ) (A := A) hA β' := by
  -- `β / β'` is a local `p`-th power
  have h1 : NK.UchidaKummer.localPowClass ↥K p 𝔭 (β * β'⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  -- hence its Kummer character is trivial, so the two characters agree
  have h2 : kummerCharMonoidHom (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
      (A := A) hA (β * β'⁻¹) = 1 :=
    (kummerCharMonoidHom_eq_one_iff (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
      (A := A) hA 𝔭 h𝔭 (β * β'⁻¹)).mpr h1
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  exact h2

end Work.SSGRoute.ZConstruction

import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.Chebotarev.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Residue degree one gives a trivial Frobenius

Let `𝔭` be a finite place of a number field `K` and `𝔔` a place of a finite extension field `E`
lying over `𝔭`.  If the residue degree `f(𝔔/𝔭)` is one, then the identity of `Gal(E/K)` is a
Frobenius element at `𝔔`: this is the converse of
`NK.CFTLib.ArtinReciprocityIdeal.residueField_card_eq_of_isFrobAt_one`, and unlike
`NK.Chebotarev.IsFrobAt_eq_one_iff_inertiaDeg_eq_one` it needs neither `[IsGalois K E]` nor
unramifiedness (a totally ramified prime has `f = 1` but `e > 1`).

Indeed `f = 1` says exactly that the two residue fields are equinumerous, and in a field of
cardinality `q` the map `y ↦ y ^ q` is the identity.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain
open scoped NumberField

namespace NK.CFTLib.ARL

theorem inertiaDeg_one_isFrobAtPrime_one {K E : Type} [Field K] [NumberField K] [Field E]
    [NumberField E] [Algebra K E] [FiniteDimensional K E] (𝔭 : NK.Chebotarev.PrimeIdeal K)
    (𝔔 : NK.Chebotarev.PrimeIdeal E) (h : 𝔔.asIdeal.LiesOver 𝔭.asIdeal)
    (hf : 𝔔.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1) :
    NK.Chebotarev.IsFrobAtPrime (K := K) (L := E) 𝔭 (1 : E ≃ₐ[K] E) := by
  letI : 𝔭.asIdeal.IsMaximal := Ring.DimensionLEOne.maximalOfPrime 𝔭.ne_bot 𝔭.isPrime
  letI : 𝔔.asIdeal.IsMaximal := Ring.DimensionLEOne.maximalOfPrime 𝔔.ne_bot 𝔔.isPrime
  haveI : Finite (NumberField.RingOfIntegers E ⧸ 𝔔.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum 𝔔
  letI : Fintype (NumberField.RingOfIntegers E ⧸ 𝔔.asIdeal) := Fintype.ofFinite _
  letI : Field (NumberField.RingOfIntegers E ⧸ 𝔔.asIdeal) := Ideal.Quotient.field _
  have hunder : Ideal.under (NumberField.RingOfIntegers K) 𝔔.asIdeal = 𝔭.asIdeal := h.over.symm
  have hcard : Nat.card (NumberField.RingOfIntegers E ⧸ 𝔔.asIdeal)
      = Nat.card (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) := by
    have h1 := Ideal.cardQuot_pow_inertiaDeg 𝔭.asIdeal 𝔔.asIdeal
    rw [hf, pow_one, Submodule.cardQuot_apply, Submodule.cardQuot_apply] at h1
    exact h1.symm
  refine ⟨𝔔, h, ?_⟩
  rw [NK.Chebotarev.isFrobAt_def]
  intro x
  have hgal : (galRestrict (NumberField.RingOfIntegers K) K E (NumberField.RingOfIntegers E)
      (1 : E ≃ₐ[K] E)) = 1 := map_one _
  rw [hgal, AlgEquiv.one_apply, hunder]
  have hy : (Ideal.Quotient.mk 𝔔.asIdeal x) ^
        Nat.card (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal)
      = Ideal.Quotient.mk 𝔔.asIdeal x := by
    rw [← hcard, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card _

  rw [← Ideal.Quotient.eq]
  rw [map_pow]
  exact hy.symm

end NK.CFTLib.ARL

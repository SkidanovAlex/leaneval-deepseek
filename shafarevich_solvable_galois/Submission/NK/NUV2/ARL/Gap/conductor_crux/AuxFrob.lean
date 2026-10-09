/-
# The Frobenius at a prime acts on `ζ_M` by the norm

Two auxiliary facts used in the construction of the auxiliary field:

* `AuxZeta_frob_pow`: an arithmetic Frobenius at a prime `𝔓 | 𝔭` of `Ω = L(ζ_M)` raises the
  primitive `M`-th root of unity `ζ_M` to the `N𝔭`-th power (this is the cyclotomic
  reciprocity law; the key point is that `M ∉ 𝔓`, which follows from the coprimality of `M`
  with `N𝔭`);
* `AuxChi_eq_absNorm`: the corresponding statement for the cyclotomic character `χ`.
-/
import Mathlib
import Submission.NK.NUV2.ARL.Gap.conductor_crux.AuxGalois
import Submission.NK.CFTLib.ARL.isFrobAtPrime_zeta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace NK.NUV2.ARL.Gap.conductor_crux

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] (M : ℕ) [NeZero M]

lemma one_lt_absNorm_aux (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    1 < Ideal.absNorm 𝔭.asIdeal := by
  haveI : 𝔭.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal 𝔭.isPrime 𝔭.ne_bot
  haveI : Field (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) := Ideal.Quotient.field 𝔭.asIdeal
  haveI : Finite (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot 𝔭.asIdeal 𝔭.ne_bot
  haveI : Fintype (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) := Fintype.ofFinite _
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

/-- If no prime divisor of `M` divides `N𝔭`, then `M` is not in `𝔭`. -/
lemma natCast_notMem_of_not_dvd_absNorm (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hcop : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ Ideal.absNorm 𝔭.asIdeal) :
    (M : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal := by
  intro hmem
  have hdiv : Ideal.absNorm 𝔭.asIdeal ∣ M ^ Module.finrank ℤ (NumberField.RingOfIntegers K) := by
    have h := Ideal.absNorm_dvd_norm_of_mem hmem
    rw [Algebra.norm_natCast] at h
    exact Int.natCast_dvd_natCast.mp (by simpa using h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (one_lt_absNorm_aux 𝔭).ne'
  have hpm : p ∣ M := hp.dvd_of_dvd_pow (dvd_trans hpd hdiv)
  exact hcop p hp hpm hpd

/-- **The Frobenius acts on `ζ_M` by `N𝔭`.** -/
theorem AuxZeta_frob_pow (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (F : (CyclotomicField M L) ≃ₐ[K] (CyclotomicField M L))
    (𝔓 : HeightOneSpectrum (NumberField.RingOfIntegers (CyclotomicField M L)))
    (h𝔓 : 𝔓.asIdeal.LiesOver 𝔭.asIdeal) (hF : NK.Chebotarev.IsFrobAt 𝔓 F)
    (hcop : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ Ideal.absNorm 𝔭.asIdeal) :
    F (AuxZeta L M) = (AuxZeta L M) ^ Ideal.absNorm 𝔭.asIdeal := by
  have hζ := AuxZeta_isPrimitiveRoot L M
  have hM𝔓 : (M : NumberField.RingOfIntegers (CyclotomicField M L)) ∉ 𝔓.asIdeal := by
    intro hmem
    have hK𝔭 : (M : NumberField.RingOfIntegers K) ∈ 𝔭.asIdeal :=
      (Ideal.mem_of_liesOver (P := 𝔓.asIdeal) (p := 𝔭.asIdeal)
        (x := (M : NumberField.RingOfIntegers K))).mpr (by simpa using hmem)
    exact natCast_notMem_of_not_dvd_absNorm M 𝔭 hcop hK𝔭
  have hζint : IsPrimitiveRoot hζ.toInteger M := hζ.toInteger_isPrimitiveRoot
  have hcoe : algebraMap (NumberField.RingOfIntegers (CyclotomicField M L))
      (CyclotomicField M L) hζ.toInteger = AuxZeta L M := hζ.coe_toInteger
  have h1 : galRestrict (NumberField.RingOfIntegers K) K (CyclotomicField M L)
        (NumberField.RingOfIntegers (CyclotomicField M L)) F hζ.toInteger =
      hζ.toInteger ^ Nat.card (NumberField.RingOfIntegers K ⧸
        𝔓.asIdeal.under (NumberField.RingOfIntegers K)) :=
    AlgHom.IsArithFrobAt.apply_of_pow_eq_one hF hζint.pow_eq_one hM𝔓
  have h2 := congrArg (algebraMap (NumberField.RingOfIntegers (CyclotomicField M L))
    (CyclotomicField M L)) h1
  rw [map_pow, algebraMap_galRestrict_apply] at h2
  rw [hcoe, ← h𝔓.over] at h2
  have h3 : Nat.card (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) = Ideal.absNorm 𝔭.asIdeal := by
    rw [Ideal.absNorm_apply]; rfl
  rw [h3] at h2
  exact h2

/-- The cyclotomic character at a Frobenius element is the norm of the prime. -/
lemma AuxChi_eq_absNorm (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (F : (CyclotomicField M L) ≃ₐ[K] (CyclotomicField M L))
    (hF : F (AuxZeta L M) = (AuxZeta L M) ^ Ideal.absNorm 𝔭.asIdeal) :
    (((AuxChi M F : (ZMod M)ˣ) : ZMod M)) = (Ideal.absNorm 𝔭.asIdeal : ZMod M) := by
  have hζ := AuxZeta_isPrimitiveRoot L M
  have hfin : IsOfFinOrder (AuxZeta L M) := hζ.isOfFinOrder (NeZero.ne M)
  have hspec := AuxChi_apply M F
  rw [hF] at hspec
  have hmod1 : (((AuxChi M F : (ZMod M)ˣ) : ZMod M)).val ≡ Ideal.absNorm 𝔭.asIdeal
      [MOD orderOf (AuxZeta L M)] := hfin.pow_eq_pow_iff_modEq.mp hspec
  have hmod : (((AuxChi M F : (ZMod M)ˣ) : ZMod M)).val ≡ Ideal.absNorm 𝔭.asIdeal
      [MOD M] := by
    rw [← hζ.eq_orderOf] at hmod1
    exact hmod1
  rw [← ZMod.natCast_zmod_val ((AuxChi M F : (ZMod M)ˣ) : ZMod M)]
  exact (ZMod.natCast_eq_natCast_iff _ _ M).mpr hmod

end NK.NUV2.ARL.Gap.conductor_crux

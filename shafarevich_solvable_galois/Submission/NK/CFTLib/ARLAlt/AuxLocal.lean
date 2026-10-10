import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Submission.NK.Chebotarev.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local auxiliary facts for the transfer (Lang X §2)

Statements about a Frobenius element equal to `1` at a prime `P` of a finite extension `M/K` of
number fields: the residue degree is `1` and `N_{M/K}(P) = P ∩ 𝓞 K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.ARLAlt

/-- **The residue field of `P` consists of the roots of `X^{#κ(p)} - X`** when the identity is a
Frobenius element at `P`. -/
theorem pow_card_eq_self_of_isFrobAt_one {K M : Type} [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [FiniteDimensional K M]
    {p : NK.Chebotarev.PrimeIdeal K} {P : NK.Chebotarev.PrimeIdeal M}
    (hP : P.asIdeal.LiesOver p.asIdeal) (h : NK.Chebotarev.IsFrobAt (K := K) (L := M) P 1) :
    ∀ y : NumberField.RingOfIntegers M ⧸ P.asIdeal,
      y ^ Nat.card (NumberField.RingOfIntegers K ⧸ p.asIdeal) = y := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hkey := h.mk_apply hP x
  rw [map_one] at hkey
  exact hkey.symm

/-- **Residue degree one from a trivial Frobenius.** -/
theorem inertiaDeg_eq_one_of_isFrobAt_one {K M : Type} [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [FiniteDimensional K M]
    {p : NK.Chebotarev.PrimeIdeal K} {P : NK.Chebotarev.PrimeIdeal M}
    (hP : P.asIdeal.LiesOver p.asIdeal) (h : NK.Chebotarev.IsFrobAt (K := K) (L := M) P 1) :
    P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1 := by
  haveI := hP
  haveI : Finite (NumberField.RingOfIntegers K ⧸ p.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum p
  haveI : Finite (NumberField.RingOfIntegers M ⧸ P.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum P
  haveI : Fintype (NumberField.RingOfIntegers K ⧸ p.asIdeal) := Fintype.ofFinite _
  haveI : Fintype (NumberField.RingOfIntegers M ⧸ P.asIdeal) := Fintype.ofFinite _
  letI : Field (NumberField.RingOfIntegers K ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
  letI : Field (NumberField.RingOfIntegers M ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  have hcard := Commons.NumberTheory.NumberField.natCard_residue_eq_pow_inertiaDeg p P hP
  have hq2 : 2 ≤ Nat.card (NumberField.RingOfIntegers K ⧸ p.asIdeal) := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  have hle : P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) ≤ 1 := by
    refine Commons.NumberTheory.NumberField.le_of_forall_pow_eq_self hcard hq2 (by norm_num)
      (fun y => ?_)
    rw [pow_one]
    exact pow_card_eq_self_of_isFrobAt_one hP h y
  have hpos := Ideal.inertiaDeg_pos P.asIdeal (NumberField.RingOfIntegers K)
  omega

/-- **The norm of a prime with trivial Frobenius is the prime below.** -/
theorem relNorm_prime_eq_of_isFrobAt_one {K M : Type} [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [FiniteDimensional K M]
    {p : NK.Chebotarev.PrimeIdeal K} {P : NK.Chebotarev.PrimeIdeal M}
    (hP : P.asIdeal.LiesOver p.asIdeal) (h : NK.Chebotarev.IsFrobAt (K := K) (L := M) P 1) :
    Ideal.relNorm (NumberField.RingOfIntegers K) P.asIdeal = p.asIdeal := by
  haveI := hP
  haveI : P.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal P.isPrime P.ne_bot
  haveI : p.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal p.isPrime p.ne_bot
  rw [Ideal.relNorm_eq_pow_of_isMaximal P.asIdeal p.asIdeal,
    inertiaDeg_eq_one_of_isFrobAt_one hP h, pow_one]

/-- **A prime of `E` above `𝔭` with trivial Frobenius.**  From the fact that some prime of `↥E`
above `𝔭` has identity Frobenius element (i.e. `𝔭` splits completely in `E/K`) we extract it, and
record that its relative norm is `𝔭` itself. -/
theorem exists_primeIdeal_isFrobAt_one {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (E : IntermediateField K L) (𝔭 : NK.Chebotarev.PrimeIdeal K)
    (h : NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥E) 𝔭 1) :
    ∃ 𝔓 : NK.Chebotarev.PrimeIdeal ↥E, 𝔓.asIdeal.LiesOver 𝔭.asIdeal ∧
      NK.Chebotarev.IsFrobAt (K := K) (L := ↥E) 𝔓 1 ∧
      Ideal.relNorm (NumberField.RingOfIntegers K) 𝔓.asIdeal = 𝔭.asIdeal := by
  obtain ⟨𝔓, hlies, hfrob⟩ := h
  exact ⟨𝔓, hlies, hfrob, relNorm_prime_eq_of_isFrobAt_one hlies hfrob⟩

/-- **A cyclotomic extension from a generating primitive root.** -/
theorem isCyclotomicExtension_of_adjoin_eq_top {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω]
    [Algebra.IsIntegral E Ω] {n : ℕ} [NeZero n] {ζ : Ω} (hζ : IsPrimitiveRoot ζ n)
    (h : IntermediateField.adjoin E ({ζ} : Set Ω) = ⊤) :
    IsCyclotomicExtension {n} E Ω := by
  haveI h1 : IsCyclotomicExtension {n} E ↥(IntermediateField.adjoin E ({ζ} : Set Ω)) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension (K := E) (L := Ω)
  rw [h] at h1
  exact IsCyclotomicExtension.equiv (S := {n}) (A := E)
    (B := ↥(⊤ : IntermediateField E Ω)) (C := Ω)
    (IntermediateField.topEquiv : ↥(⊤ : IntermediateField E Ω) ≃ₐ[E] Ω)

/-- **`Ω/E` is Galois when it contains a finite Galois extension `L/k` with `L ⊔ E = ⊤`.** -/
theorem isGalois_sup_right_of_isGalois {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L E : IntermediateField K Ω) [IsGalois K L] [FiniteDimensional K L]
    (h : L ⊔ E = ⊤) : IsGalois ↥E Ω :=
  IsGalois.sup_right L E h

end NK.CFTLib.ARLAlt

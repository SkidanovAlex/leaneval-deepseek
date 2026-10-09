import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.SimpleRing.Principal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation

open scoped NumberField

open IsDedekindDomain

/-- Membership in `valuationSubringAtPrime`: an element of the fraction field lies in the
localization of `R` at `v` (as a valuation subring) iff it can be written `a / s` with
`a : R` and `s` outside the prime `v`. -/
lemma mem_valuationSubringAtPrime {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*}
    [Field K] [Algebra R K] [IsFractionRing R K]
    (v : IsDedekindDomain.HeightOneSpectrum R) (x : K) :
    x ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v ↔
      ∃ a s : R, ∃ (_ : s ∈ v.asIdeal.primeCompl),
        x = algebraMap R K a * (algebraMap R K s)⁻¹ := by
  rw [show x ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v ↔
      x ∈ (Localization.subalgebra.ofField K v.asIdeal.primeCompl
        v.asIdeal.primeCompl_le_nonZeroDivisors).toSubring from Iff.rfl]
  rw [Subalgebra.mem_toSubring]
  exact Iff.rfl

theorem exists_heightOneSpectrum_eq_valuationSubringAtPrime {L : Type*} [Field L] [NumberField L]
    (A : ValuationSubring L) (hA : A ≠ ⊤)
    (hR : ∀ x : NumberField.RingOfIntegers L,
      algebraMap (NumberField.RingOfIntegers L) L x ∈ A) :
    ∃ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      A = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L P := by
  let φ : NumberField.RingOfIntegers L →+* A :=
    { toFun := fun x => ⟨algebraMap (NumberField.RingOfIntegers L) L x, hR x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  let P : Ideal (NumberField.RingOfIntegers L) := Ideal.comap φ (IsLocalRing.maximalIdeal A)
  have hmaxprime : (IsLocalRing.maximalIdeal A).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal A).isPrime
  have hPprime : P.IsPrime := Ideal.comap_isPrime φ (IsLocalRing.maximalIdeal A)
  -- Produce a nonzero element of the number ring whose image lies in the maximal ideal of `A`.
  obtain ⟨x, hx⟩ : ∃ x : L, x ∉ A := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hA (le_antisymm le_top fun y _ => h y)
  have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ A.zero_mem)
  have hxinv : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hx
  have hval : 1 < A.valuation x := lt_of_not_ge fun h => hx ((A.valuation_le_one_iff x).mp h)
  have hmem : (⟨x⁻¹, hxinv⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [A.valuation_lt_one_iff]
    show A.valuation x⁻¹ < 1
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hval
  obtain ⟨a, b, hb, hab⟩ :=
    IsFractionRing.div_surjective (NumberField.RingOfIntegers L) x⁻¹
  have hb0 : algebraMap (NumberField.RingOfIntegers L) L b ≠ 0 := fun h =>
    nonZeroDivisors.ne_zero hb (IsFractionRing.injective (NumberField.RingOfIntegers L) L
      (by rw [h, map_zero]))
  have hmul : algebraMap (NumberField.RingOfIntegers L) L a =
      x⁻¹ * algebraMap (NumberField.RingOfIntegers L) L b := by
    rw [← hab, div_mul_cancel₀ _ hb0]
  have ha0 : a ≠ 0 := by
    intro ha
    have : x⁻¹ = 0 := by
      have h1 := hmul
      rw [ha, map_zero] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_right hb0
    exact hx0 (inv_eq_zero.mp this)
  have hφa : φ a = (⟨x⁻¹, hxinv⟩ : A) * φ b := by
    apply Subtype.ext
    show algebraMap (NumberField.RingOfIntegers L) L a =
      x⁻¹ * algebraMap (NumberField.RingOfIntegers L) L b
    exact hmul
  have hφa_mem : φ a ∈ IsLocalRing.maximalIdeal A := by
    rw [hφa]
    exact Ideal.mul_mem_right (φ b) (IsLocalRing.maximalIdeal A) hmem
  have hPne : P ≠ ⊥ := by
    intro hbot
    have : a ∈ P := (Ideal.mem_comap (f := φ)).mpr hφa_mem
    rw [hbot] at this
    exact ha0 (Ideal.mem_bot.mp this)
  let P' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) := ⟨P, hPprime, hPne⟩
  refine ⟨P', ?_⟩
  have hle : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L P' ≤ A := by
    intro x hx
    obtain ⟨a, s, hs, rfl⟩ := (mem_valuationSubringAtPrime P' x).mp hx
    have hsP : s ∉ P := Ideal.mem_primeCompl_iff.mp hs
    have hnot : φ s ∉ IsLocalRing.maximalIdeal A :=
      fun hc => hsP ((Ideal.mem_comap (f := φ)).mpr hc)
    have hunit : IsUnit (φ s) := (IsLocalRing.notMem_maximalIdeal).mp hnot
    have hval2 : A.valuation (algebraMap (NumberField.RingOfIntegers L) L s) = 1 := by
      have h2 := (A.valuation_eq_one_iff (φ s)).mp hunit
      rwa [show ((φ s : A) : L) = algebraMap (NumberField.RingOfIntegers L) L s from rfl] at h2
    have hsinv : (algebraMap (NumberField.RingOfIntegers L) L s)⁻¹ ∈ A := by
      rw [← A.valuation_le_one_iff, map_inv₀, hval2, inv_one]
    exact A.mul_mem _ _ (hR a) hsinv
  exact (ValuationSubring.eq_of_le_of_ne_top
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L P') hle hA).symm

end Commons.RingTheory.Valuation
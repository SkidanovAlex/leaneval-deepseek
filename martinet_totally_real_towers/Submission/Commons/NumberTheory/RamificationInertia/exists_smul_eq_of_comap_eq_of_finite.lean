import Mathlib
import Submission.Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top
import Submission.Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
import Submission.Commons.RingTheory.Valuation.comap_valuationSubringAtPrime
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
import Submission.Commons.NumberTheory.RamificationInertia.exists_smul_valuationSubringAtPrime_eq

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.RamificationInertia

open scoped Pointwise

/-- **Finite-level transitivity of the Galois action on places, valuation-ring form.**  In a
finite Galois extension `L / F` of number fields, two proper valuation subrings `P`, `Q` of `L`
with the same trace on `F` are conjugate under `Gal(L/F)`.

Suggested route: `P` and `Q` are automatically the valuation rings of places of `L`
(`Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top` together with
`Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime`), the places
below them are equal (`Commons.RingTheory.Valuation.comap_valuationSubringAtPrime` and
`Commons.RingTheory.Valuation.valuationSubringAtPrime_injective`), and then apply
`Commons.NumberTheory.RamificationInertia.exists_smul_valuationSubringAtPrime_eq`. -/
theorem exists_smul_eq_of_comap_eq_of_finite {F L : Type*} [Field F] [NumberField F] [Field L]
    [NumberField L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (P Q : ValuationSubring L) (hP : P ≠ ⊤) (hQ : Q ≠ ⊤)
    (h : P.comap (algebraMap F L) = Q.comap (algebraMap F L)) :
    ∃ σ : L ≃ₐ[F] L, σ • P = Q := by
  -- `P` and `Q` are the valuation rings of places `w₁`, `w₂` of `L`.
  obtain ⟨w₁, hw₁⟩ :=
    Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime (L := L)
      P hP (Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top P hP)
  obtain ⟨w₂, hw₂⟩ :=
    Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime (L := L)
      Q hQ (Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top Q hQ)
  -- The places of `F` below them.
  let p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) :=
    IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers F) w₁
  let p₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) :=
    IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers F) w₂
  have hlie₁ : w₁.asIdeal.LiesOver p.asIdeal := by
    change w₁.asIdeal.LiesOver (w₁.asIdeal.under (NumberField.RingOfIntegers F))
    exact ⟨rfl⟩
  have hlie₂' : w₂.asIdeal.LiesOver p₂.asIdeal := by
    change w₂.asIdeal.LiesOver (w₂.asIdeal.under (NumberField.RingOfIntegers F))
    exact ⟨rfl⟩
  -- Their valuation rings are the traces of `P` and `Q` on `F`.
  have hPp : P.comap (algebraMap F L) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F p := by
    rw [hw₁]
    exact Commons.RingTheory.Valuation.comap_valuationSubringAtPrime p w₁ hlie₁
  have hQp : Q.comap (algebraMap F L) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F p₂ := by
    rw [hw₂]
    exact Commons.RingTheory.Valuation.comap_valuationSubringAtPrime p₂ w₂ hlie₂'
  -- Hence `p = p₂`: the two places have the same trace on `F`.
  have hpq : p = p₂ := by
    apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
      (R := NumberField.RingOfIntegers F) (K := F)
    rw [← hPp, h, hQp]
  -- So both `w₁` and `w₂` lie over the same place `p` of `F`.
  have hlie₂ : w₂.asIdeal.LiesOver p.asIdeal := by
    refine ⟨?_⟩
    show p.asIdeal = w₂.asIdeal.under (NumberField.RingOfIntegers F)
    rw [hpq]
    rfl
  haveI : w₂.asIdeal.LiesOver p.asIdeal := hlie₂
  -- Galois transitivity of the action on the places over `p`.
  obtain ⟨σ, hσ⟩ := exists_smul_valuationSubringAtPrime_eq p w₁ w₂
  refine ⟨σ, ?_⟩
  rw [hw₁, hw₂]
  exact hσ

end Commons.NumberTheory.RamificationInertia

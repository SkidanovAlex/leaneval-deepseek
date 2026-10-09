import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.FieldTheory.Galois.exists_mem_stabilizer_restrictNormalHom_eq
import Submission.Commons.RingTheory.Valuation.comap_valuationSubringAtPrime
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top
import Submission.Commons.RingTheory.DedekindDomain.valuation_map_of_map_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false

open scoped NumberField Pointwise

namespace Commons.NumberTheory.NumberField.Completion

section General

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] [IsGalois F E]

/-- **The valuation of the place `σ • w` at `σ x` is the valuation of `w` at `x`.** -/
private theorem valuation_placeSmul (σ : Gal(E/F))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (x : E) :
    IsDedekindDomain.HeightOneSpectrum.valuation E (placeSmul σ w) (σ x) =
      IsDedekindDomain.HeightOneSpectrum.valuation E w x :=
  Commons.RingTheory.DedekindDomain.valuation_map_of_map_eq
    (R := NumberField.RingOfIntegers E) (K := E)
    (galRestrict (NumberField.RingOfIntegers F) F E (NumberField.RingOfIntegers E) σ :
      NumberField.RingOfIntegers E ≃+* NumberField.RingOfIntegers E)
    σ.toRingEquiv
    (fun r => (algebraMap_galRestrict_apply (NumberField.RingOfIntegers F) σ r).symm)
    w (placeSmul σ w) (placeSmul_asIdeal σ w) x

/-- **The stabiliser of the valuation ring of a finite place is its decomposition group.** -/
private theorem mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (σ : Gal(E/F)) :
    σ ∈ MulAction.stabilizer (Gal(E/F))
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E w) ↔
      σ ∈ decompositionSubgroup (K := F) w := by
  have hmem : ∀ y : E,
      (y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E w ↔
        IsDedekindDomain.HeightOneSpectrum.valuation E w y ≤ 1) := by
    intro y
    rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      Valuation.mem_valuationSubring_iff]
  constructor
  · intro h
    rw [MulAction.mem_stabilizer_iff] at h
    have hstab : ∀ y : E,
        (y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E w ↔
          σ y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E w) := by
      intro y
      have hy : σ y ∈ σ • IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E w ↔
          σ⁻¹ • (σ y) ∈
            IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E w :=
        ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
      rw [h] at hy
      simpa using hy.symm
    rw [mem_decompositionSubgroup]
    refine IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := E) ?_
    rw [Valuation.isEquiv_iff_val_le_one]
    intro y
    obtain ⟨x, rfl⟩ := σ.surjective y
    rw [valuation_placeSmul σ w x]
    exact (hmem x).symm.trans ((hstab x).trans (hmem (σ x)))
  · intro h
    rw [mem_decompositionSubgroup] at h
    rw [MulAction.mem_stabilizer_iff]
    refine SetLike.ext fun y => ?_
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    have hkey : IsDedekindDomain.HeightOneSpectrum.valuation E w (σ⁻¹ • y) =
        IsDedekindDomain.HeightOneSpectrum.valuation E w y := by
      have h2 := valuation_placeSmul (F := F) σ w (σ⁻¹ • y)
      rw [h] at h2
      simpa using h2.symm
    have hy : σ⁻¹ • y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E w ↔
        IsDedekindDomain.HeightOneSpectrum.valuation E w (σ⁻¹ • y) ≤ 1 := hmem _
    have hy' : y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E w ↔
        IsDedekindDomain.HeightOneSpectrum.valuation E w y ≤ 1 := hmem _
    rw [hy, hy', hkey]

end General

theorem exists_mem_decompositionSubgroup_restrictNormalHom_eq {K M : Type*} [Field K]
    [NumberField K] [Field M] [NumberField M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (L : IntermediateField K M) [FiniteDimensional K L] [Normal K L] [IsGalois K ↥L]
    (wL : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    (hwL : wL.asIdeal = w.asIdeal.under (NumberField.RingOfIntegers L))
    (hlies : w.asIdeal.LiesOver wL.asIdeal)
    (τ : Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) wL) :
    ∃ σ : Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) w,
      AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L σ.1 = τ.1 := by
  set A : ValuationSubring M :=
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M w with hA
  -- The trace of `A` on the base field `K` is the valuation ring of the place below `w`, so
  -- it is a proper subring.
  have hC : A.comap (algebraMap K M) ≠ ⊤ := by
    have h1 : A.comap (algebraMap K M) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K
          (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) w) := by
      rw [hA]
      exact Commons.RingTheory.Valuation.comap_valuationSubringAtPrime
        (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) w) w (by
          change w.asIdeal.LiesOver
            (w.asIdeal.under (NumberField.RingOfIntegers K))
          exact ⟨rfl⟩)
    rw [h1]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top _
  -- The trace of `A` on `L` is the valuation ring of the place `wL` below `w`.
  have hcomapL : A.comap (algebraMap ↥L M) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L wL := by
    rw [hA]
    exact Commons.RingTheory.Valuation.comap_valuationSubringAtPrime wL w hlies
  -- An element of the decomposition group of `wL` stabilises this trace.
  have hτ : τ.1 ∈ MulAction.stabilizer (↥L ≃ₐ[K] ↥L) (A.comap (algebraMap ↥L M)) := by
    rw [hcomapL]
    exact (mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup
      (F := K) (E := ↥L) wL τ.1).mpr τ.2
  -- Transitivity of the Galois action on the places over `wL` (in the valuation-ring form)
  -- lifts `τ` to an element of `Gal(M/K)` stabilising `A`.
  obtain ⟨σ, hσA, hστ⟩ := Commons.FieldTheory.Galois.exists_mem_stabilizer_restrictNormalHom_eq
    (F := K) (K' := M) A hC L τ.1 hτ
  refine ⟨⟨σ, ?_⟩, hστ⟩
  rw [hA] at hσA
  exact (mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup
    (F := K) (E := M) w σ).mp hσA

end Commons.NumberTheory.NumberField.Completion

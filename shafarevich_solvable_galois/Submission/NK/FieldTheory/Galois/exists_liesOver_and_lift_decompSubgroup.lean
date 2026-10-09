import Mathlib
import Submission.NK.FieldTheory.Galois.DecompDefs
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.FieldTheory.Galois

open scoped NumberField Pointwise

theorem exists_liesOver_and_lift_decompSubgroup {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (F : IntermediateField K L) [Normal K F]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥F))
    (σ : ↥F ≃ₐ[K] ↥F) (hσ : σ ∈ NK.FieldTheory.Galois.decompSubgroup (K := K) q) :
    ∃ (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) (σ' : L ≃ₐ[K] L),
      P.asIdeal.LiesOver q.asIdeal ∧
      AlgEquiv.restrictNormalHom (F := K) (K₁ := L) F σ' = σ ∧
      σ' ∈ NK.FieldTheory.Galois.decompSubgroup (K := K) P := by
  -- Choose a finite place `P` of `L` above `q`.
  obtain ⟨P, hP⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := ↥F) (L := L) q
  refine ⟨P, ?_⟩
  -- The valuation ring of `P` restricts to the valuation ring of `q`.
  set A : ValuationSubring L :=
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L P with hA
  have hcomap : A.comap (algebraMap ↥F L) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥F q := by
    rw [hA]
    exact Commons.RingTheory.Valuation.comap_valuationSubringAtPrime q P hP
  -- Hence it is a proper valuation subring of `L`.
  have hC : A.comap (algebraMap K L) ≠ ⊤ := by
    have hcomp : (algebraMap ↥F L).comp (algebraMap K ↥F) = algebraMap K L := by
      ext x
      exact (IsScalarTower.algebraMap_apply K ↥F L x).symm
    have h1 : A.comap (algebraMap K L) =
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥F q).comap
          (algebraMap K ↥F) := by
      calc A.comap (algebraMap K L)
          = A.comap ((algebraMap ↥F L).comp (algebraMap K ↥F)) := by rw [hcomp]
        _ = (A.comap (algebraMap ↥F L)).comap (algebraMap K ↥F) :=
            (ValuationSubring.comap_comap A (algebraMap ↥F L) (algebraMap K ↥F)).symm
        _ = (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥F q).comap
              (algebraMap K ↥F) := by rw [hcomap]
    rw [h1, Commons.RingTheory.Valuation.comap_valuationSubringAtPrime
      (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) q) q (by
        change q.asIdeal.LiesOver (q.asIdeal.under (NumberField.RingOfIntegers K))
        exact ⟨rfl⟩)]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top _
  -- `σ` stabilises the trace of `A` on `F`.
  have hτ : σ ∈ MulAction.stabilizer (↥F ≃ₐ[K] ↥F) (A.comap (algebraMap ↥F L)) := by
    rw [hcomap]
    exact (mem_stabilizer_valuationSubringAtPrime_iff_mem_decompSubgroup q σ).mpr hσ
  -- Lift `σ` to a `K`-automorphism of `L` stabilising `A`.
  obtain ⟨σ', hσ'A, hσ'res⟩ :=
    Commons.RingTheory.Valuation.exists_mem_stabilizer_restrictNormalHom_eq_of_isGalois
      (F := K) (E := L) A hC F σ hτ
  refine ⟨σ', hP, hσ'res, ?_⟩
  rw [hA] at hσ'A
  exact (mem_stabilizer_valuationSubringAtPrime_iff_mem_decompSubgroup P σ').mp hσ'A

end NK.FieldTheory.Galois

import Mathlib
import Submission.NK.FieldTheory.Galois.DecompDefs
import Submission.Commons.RingTheory.Valuation.exists_mem_stabilizer_restrictNormalHom_eq_of_isGalois
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.FieldTheory.Galois

open scoped Pointwise

theorem exists_mem_map_decompSubgroup {K K' : Type*} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (H : Subgroup Gal(K'/K))
    (h : ∀ A : ValuationSubring K', A.comap (algebraMap K K') ≠ ⊤ →
      ∀ g : Gal(K'/K), A.comap (g : K' →+* K') = A → g ∈ H)
    (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L)) :
    ∀ τ : ↥L ≃ₐ[K] ↥L, τ ∈ NK.FieldTheory.Galois.decompSubgroup (K := K) w →
      ∃ σ ∈ H, AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ = τ := by
  intro τ hτ
  set V : ValuationSubring ↥L :=
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L w with hV
  -- Extend the valuation ring of `w` to a valuation subring `A` of `K'`.
  obtain ⟨A, hA⟩ := Commons.RingTheory.Valuation.exists_valuationSubring_comap_eq
    (K := ↥L) (L := K') V
  -- The trace of `A` on the base field `K` is the valuation ring of the place below `w`.
  have hcomp : (algebraMap ↥L K').comp (algebraMap K ↥L) = algebraMap K K' := by
    ext x
    exact IsScalarTower.algebraMap_apply K ↥L K' x
  have hAk : A.comap (algebraMap K K') = V.comap (algebraMap K ↥L) := by
    rw [← hA, ValuationSubring.comap_comap, hcomp]
  have hVne : V.comap (algebraMap K ↥L) ≠ ⊤ := by
    rw [hV, Commons.RingTheory.Valuation.comap_valuationSubringAtPrime
      (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) w) w (by
        change w.asIdeal.LiesOver
          (w.asIdeal.under (NumberField.RingOfIntegers K))
        exact ⟨rfl⟩)]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top _
  have hC : A.comap (algebraMap K K') ≠ ⊤ := by rw [hAk]; exact hVne
  -- An element of the decomposition group of `w` stabilises the trace of `A` on `L`.
  have hτ' : τ ∈ MulAction.stabilizer (↥L ≃ₐ[K] ↥L) (A.comap (algebraMap ↥L K')) := by
    rw [hA]
    exact (mem_stabilizer_valuationSubringAtPrime_iff_mem_decompSubgroup w τ).mpr hτ
  -- Surjectivity of the restriction of the stabiliser of `A` onto the stabiliser of the trace.
  obtain ⟨σ, hσA, hστ⟩ :=
    Commons.RingTheory.Valuation.exists_mem_stabilizer_restrictNormalHom_eq_of_isGalois
      (F := K) (E := K') A hC L τ hτ'
  refine ⟨σ, ?_, hστ⟩
  -- `σ⁻¹` also stabilises `A`, hence lies in `H` by hypothesis.
  have h2 : A.comap (σ.symm : K' →+* K') = A := by
    rw [← Submission.NeukirchUchida.Local.smul_eq_comap_symm_alg A σ]
    exact MulAction.mem_stabilizer_iff.mp hσA
  have hmem : σ.symm ∈ H := h A hC σ.symm h2
  have hmem' : (σ.symm)⁻¹ ∈ H := H.inv_mem hmem
  rw [AlgEquiv.aut_inv, AlgEquiv.symm_symm] at hmem'
  exact hmem'

end NK.FieldTheory.Galois

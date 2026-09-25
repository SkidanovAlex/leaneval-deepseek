import Mathlib
import Submission.Commons.RingTheory.Valuation.exists_unit_of_stabilizer_valuationSubring
import Submission.Commons.RingTheory.Valuation.val_eq_of_algEquiv_of_comap_eq
import Submission.Commons.RingTheory.Valuation.mem_stabilizer_valuationSubring_iff

namespace Commons.RingTheory.Valuation

open scoped Pointwise

/-- A finite product of elements `< 1` of a linearly ordered commutative group with zero is `< 1`.
(Only the nonempty case is meaningful; `∏ = 1` for the empty finset.) -/
private lemma finset_prod_lt_one_of_lt_one {M : Type*} [LinearOrderedCommGroupWithZero M]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → M)
    (hlt : ∀ i ∈ s, f i < 1) (hne : s.Nonempty) : ∏ i ∈ s, f i < 1 := by
  obtain ⟨i0, hi0⟩ := hne
  rw [← Finset.mul_prod_erase s f hi0]
  refine mul_lt_one_of_nonneg_of_lt_one_left zero_le (hlt i0 hi0) ?_
  exact Finset.prod_le_one₀ (fun i _ => zero_le)
    (fun i hi => (hlt i (Finset.mem_of_mem_erase hi)).le)

theorem exists_mem_fixedField_stabilizer_val_eq_one_val_lt_one {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (A : ValuationSubring L) :
    ∃ a : L, a ∈ IntermediateField.fixedField (MulAction.stabilizer (L ≃ₐ[K] L) A) ∧
      A.valuation a = 1 ∧
      ∀ σ : L ≃ₐ[K] L, σ ∉ MulAction.stabilizer (L ≃ₐ[K] L) A → A.valuation (σ a) < 1 := by
  classical
  -- `u` is a unit of `A` that is a nonunit at every other conjugate of `A`.
  obtain ⟨u, hu1, hu2⟩ := exists_unit_of_stabilizer_valuationSubring (K := K) A
  -- `D` is the decomposition group of `A`, and `a` is the norm of `u` over its fixed field.
  let D := MulAction.stabilizer (L ≃ₐ[K] L) A
  letI : Fintype D := Fintype.ofFinite D
  refine ⟨∏ σ : D, (σ : L ≃ₐ[K] L) u, ?_, ?_, ?_⟩
  · -- `a` is fixed by `D`, since multiplication by an element of `D` permutes the factors.
    rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    show τ (∏ σ : D, (σ : L ≃ₐ[K] L) u) = ∏ σ : D, (σ : L ≃ₐ[K] L) u
    rw [map_prod]
    refine Fintype.prod_equiv (Equiv.mulLeft (⟨τ, hτ⟩ : D))
      (fun σ : D => τ ((σ : L ≃ₐ[K] L) u)) (fun σ : D => (σ : L ≃ₐ[K] L) u) ?_
    intro σ
    simp [Equiv.mulLeft]
  · -- The value of `a` is the product of the values of the factors, each of which is `1`.
    have halg : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    have hval_smul : ∀ σ : D, A.valuation ((σ : L ≃ₐ[K] L) u) = 1 := by
      intro σ
      have hσmem : (σ : L ≃ₐ[K] L) ∈ MulAction.stabilizer (L ≃ₐ[K] L) A := σ.2
      have hcomap : A.comap ((σ : L ≃ₐ[K] L) : L →+* L) = A := by
        ext x
        rw [ValuationSubring.mem_comap]
        exact ((mem_stabilizer_valuationSubring_iff A (σ : L ≃ₐ[K] L)).mp hσmem x).symm
      rw [val_eq_of_algEquiv_of_comap_eq halg A (σ : L ≃ₐ[K] L) hcomap u, hu1]
    rw [map_prod]
    simp [hval_smul]
  · -- For `σ ∉ D`, every factor `σ * τ` leaves `D`, hence has value `< 1`, and the product `< 1`.
    intro σ hσ
    have hprod : σ (∏ τ : D, (τ : L ≃ₐ[K] L) u) = ∏ τ : D, σ ((τ : L ≃ₐ[K] L) u) :=
      map_prod σ _ _
    rw [hprod, map_prod]
    refine finset_prod_lt_one_of_lt_one Finset.univ _ ?_ Finset.univ_nonempty
    intro τ _
    have hnotmem : σ * (τ : L ≃ₐ[K] L) ∉ D := by
      intro h
      apply hσ
      have hτ : (τ : L ≃ₐ[K] L) ∈ D := τ.2
      have hmem : (σ * (τ : L ≃ₐ[K] L)) * (τ : L ≃ₐ[K] L)⁻¹ ∈ D := mul_mem h (inv_mem hτ)
      have heq : (σ * (τ : L ≃ₐ[K] L)) * (τ : L ≃ₐ[K] L)⁻¹ = σ := by group
      rwa [heq] at hmem
    have := hu2 (σ * (τ : L ≃ₐ[K] L)) hnotmem
    rwa [AlgEquiv.mul_apply] at this

end Commons.RingTheory.Valuation

import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Commons.NumberTheory.NumberField.Valuation.centralizer_stabilizer_valuationSubring_sepClosure
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise NumberField

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Commons.NumberTheory.NumberField.Valuation

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']

/-- If a base-preserving automorphism `σ` conjugates the stabiliser of `A` into itself, then the
conjugate `σ τ σ⁻¹` of an element `τ` of the stabiliser lies in the stabiliser of `σ • A`. -/
theorem conj_mem_stabilizer_smul (A : ValuationSubring K') (σ τ : Gal(K'/K))
    (hτ : τ ∈ MulAction.stabilizer (Gal(K'/K)) A) :
    σ * τ * σ⁻¹ ∈ MulAction.stabilizer (Gal(K'/K)) (σ • A) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact ⟨τ, hτ, by simp⟩

/-- **Normaliser vs. stabiliser of a place of the separable closure** (CoNF XII (12.1.4), the
normaliser form): an element of `Gal(K'/K)` normalising the decomposition group of a place `A` over
a finite prime `p` of the number field `K` already lies in that decomposition group.

The proof is the same rigidity argument as for the centraliser form: conjugating by `σ` identifies
the stabiliser of `A` with that of `σ • A`; if `σ • A ≠ A` the two stabilisers are disjoint
(`Commons.NumberTheory.NumberField.Valuation.stabilizer_inf_stabilizer_eq_bot_of_ne`), while the
stabiliser of `A` is nontrivial
(`Commons.NumberTheory.NumberField.Valuation.exists_ne_one_comap_eq_of_comap_ne_top`); conjugating a
nontrivial element of the stabiliser of `A` then yields a contradiction. -/
theorem normalizer_stabilizer_valuationSubring_sepClosure {K K' : Type*} [Field K]
    [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    (σ : K' ≃ₐ[K] K')
    (hσ : ∀ τ : K' ≃ₐ[K] K', A.comap (τ : K' →+* K') = A →
      A.comap ((σ * τ * σ⁻¹ : K' ≃ₐ[K] K') : K' →+* K') = A) :
    A.comap (σ : K' →+* K') = A := by
  have htop : A.comap (algebraMap K K') ≠ ⊤ := by
    rw [hA]; exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top p
  -- `hσ` in terms of the stabiliser of `A`
  have hσH : ∀ τ ∈ MulAction.stabilizer (Gal(K'/K)) A,
      σ * τ * σ⁻¹ ∈ MulAction.stabilizer (Gal(K'/K)) A := by
    intro τ hτ
    exact (comap_eq_iff_mem_stabilizer A (σ * τ * σ⁻¹)).mp
      (hσ τ ((comap_eq_iff_mem_stabilizer A τ).mpr hτ))
  have hne : σ • A = A := by
    by_contra h
    have htop' : (σ • A).comap (algebraMap K K') ≠ ⊤ := by
      rw [comap_smul_algebraMap]; exact htop
    -- the two stabilisers are disjoint because the places differ
    have hbot : MulAction.stabilizer (Gal(K'/K)) (σ • A) ⊓
        MulAction.stabilizer (Gal(K'/K)) A = ⊥ :=
      stabilizer_inf_stabilizer_eq_bot_of_ne h htop' htop
    -- a nontrivial element of the stabiliser of `A`
    obtain ⟨τ, hτne, hτmem⟩ :=
      Commons.NumberTheory.NumberField.Valuation.exists_ne_one_comap_eq_of_comap_ne_top A htop
    have hτH : τ ∈ MulAction.stabilizer (Gal(K'/K)) A :=
      (comap_eq_iff_mem_stabilizer A τ).mp hτmem
    have hmem : σ * τ * σ⁻¹ ∈ (⊥ : Subgroup (Gal(K'/K))) := by
      rw [← hbot]
      exact ⟨conj_mem_stabilizer_smul A σ τ hτH, hσH τ hτH⟩
    have hone : σ * τ * σ⁻¹ = 1 := Subgroup.mem_bot.mp hmem
    refine hτne ?_
    apply (MulAut.conj σ).injective
    rw [map_one]
    simpa [MulAut.conj_apply] using hone
  have hmem : σ ∈ MulAction.stabilizer (Gal(K'/K)) A := by
    rw [MulAction.mem_stabilizer_iff]; exact hne
  exact (comap_eq_iff_mem_stabilizer A σ).mpr hmem

end Commons.NumberTheory.NumberField.Valuation

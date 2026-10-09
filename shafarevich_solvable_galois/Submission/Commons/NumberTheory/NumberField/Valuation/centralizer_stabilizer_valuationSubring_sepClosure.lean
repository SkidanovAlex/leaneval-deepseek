import Mathlib
import Submission.Commons.RingTheory.Valuation.ValuationSubring.smul_eq_comap_symm
import Submission.Commons.RingTheory.Valuation.mem_stabilizer_valuationSubring_iff
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top
import Submission.Commons.NumberTheory.NumberField.Valuation.exists_ne_one_comap_eq_of_comap_ne_top
import Submission.Commons.NumberTheory.NumberField.Valuation.eq_one_of_comap_eq_of_comap_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Rigidity of places of the separable closure of a number field

CoNF XII (12.1.4): an element of `Gal(K'/K)` which commutes with every element of the decomposition
group of a place `A` of the separable closure `K'` of a number field `K` already lies in that
decomposition group.

The two arithmetic inputs are the *disjointness of decomposition groups of distinct places*
(CoNF XII (12.1.3), `Commons.NumberTheory.NumberField.Valuation.eq_one_of_comap_eq_of_comap_eq`)
and the *nontriviality of a decomposition group*
(`Commons.NumberTheory.NumberField.Valuation.exists_ne_one_comap_eq_of_comap_ne_top`).
-/

open scoped Pointwise NumberField

set_option linter.unusedSectionVars false

namespace Commons.NumberTheory.NumberField.Valuation

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']

/-- `A.comap τ = A` is membership in the stabiliser of `A` under the pointwise action. -/
theorem comap_eq_iff_mem_stabilizer (A : ValuationSubring K') (τ : Gal(K'/K)) :
    (A.comap (τ : K' →+* K') = A) ↔ τ ∈ MulAction.stabilizer (Gal(K'/K)) A := by
  rw [Commons.RingTheory.Valuation.mem_stabilizer_valuationSubring_iff A τ]
  constructor
  · intro h x
    have hx := SetLike.ext_iff.mp h x
    rw [ValuationSubring.mem_comap] at hx
    exact hx.symm
  · intro h
    ext x
    rw [ValuationSubring.mem_comap]
    exact (h x).symm

/-- An element commuting with the stabiliser of `A` has the same stabiliser on `σ • A`. -/
theorem stabilizer_smul_eq (A : ValuationSubring K') (σ : Gal(K'/K))
    (hcomm : ∀ τ ∈ MulAction.stabilizer (Gal(K'/K)) A, σ * τ = τ * σ) :
    MulAction.stabilizer (Gal(K'/K)) (σ • A) = MulAction.stabilizer (Gal(K'/K)) A := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  have hmap : (MulAction.stabilizer (Gal(K'/K)) A).map (MulAut.conj σ).toMonoidHom =
      MulAction.stabilizer (Gal(K'/K)) A := by
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hcomm y hy, mul_assoc, mul_inv_cancel, mul_one]
      exact hy
    · intro hx
      exact ⟨x, hx, by rw [hcomm x hx]; group⟩
  rw [hmap]

/-- A place and its image under a base-preserving automorphism have the same trace on the base. -/
theorem comap_smul_algebraMap (A : ValuationSubring K') (σ : Gal(K'/K)) :
    (σ • A).comap (algebraMap K K') = A.comap (algebraMap K K') := by
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have hfix : (σ⁻¹ : Gal(K'/K)) • (algebraMap K K' x) = algebraMap K K' x := by
    rw [AlgEquiv.smul_def]; exact (σ⁻¹).commutes x
  rw [hfix]

/-- **Reduction.** The rigidity statement follows from the disjointness of decomposition groups
of distinct places, the nontriviality of a decomposition group being
`Commons.NumberTheory.NumberField.Valuation.exists_ne_one_comap_eq_of_comap_ne_top`. -/
theorem centralizer_stabilizer_of_disjoint [IsSepClosure K K']
    (hdisj : ∀ A₁ A₂ : ValuationSubring K', A₁ ≠ A₂ →
      A₁.comap (algebraMap K K') ≠ ⊤ → A₂.comap (algebraMap K K') ≠ ⊤ →
      MulAction.stabilizer (Gal(K'/K)) A₁ ⊓ MulAction.stabilizer (Gal(K'/K)) A₂ = ⊥)
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    (σ : Gal(K'/K))
    (hσ : ∀ τ : Gal(K'/K), A.comap (τ : K' →+* K') = A → σ * τ = τ * σ) :
    A.comap (σ : K' →+* K') = A := by
  have htop : A.comap (algebraMap K K') ≠ ⊤ := by
    rw [hA]; exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top p
  have hcomm : ∀ τ ∈ MulAction.stabilizer (Gal(K'/K)) A, σ * τ = τ * σ := by
    intro τ hτ
    exact hσ τ ((comap_eq_iff_mem_stabilizer A τ).mpr hτ)
  have hstab : MulAction.stabilizer (Gal(K'/K)) (σ • A) =
      MulAction.stabilizer (Gal(K'/K)) A := stabilizer_smul_eq A σ hcomm
  have htop' : (σ • A).comap (algebraMap K K') ≠ ⊤ := by
    rw [comap_smul_algebraMap]; exact htop
  have hne : σ • A = A := by
    by_contra h
    have hbot : MulAction.stabilizer (Gal(K'/K)) (σ • A) ⊓
        MulAction.stabilizer (Gal(K'/K)) A = ⊥ := hdisj (σ • A) A h htop' htop
    rw [hstab, inf_idem] at hbot
    obtain ⟨τ, hτne, hτmem⟩ :=
      Commons.NumberTheory.NumberField.Valuation.exists_ne_one_comap_eq_of_comap_ne_top A htop
    have hτstab : τ ∈ MulAction.stabilizer (Gal(K'/K)) A :=
      (comap_eq_iff_mem_stabilizer A τ).mp hτmem
    rw [hbot] at hτstab
    exact hτne (Subgroup.mem_bot.mp hτstab)
  have hmem : (σ⁻¹ : Gal(K'/K)) ∈ MulAction.stabilizer (Gal(K'/K)) A := by
    rw [MulAction.mem_stabilizer_iff]
    have h2 : (σ⁻¹ : Gal(K'/K)) • (σ • A) = (σ⁻¹ : Gal(K'/K)) • A := by rw [hne]
    rw [smul_smul, inv_mul_cancel, one_smul] at h2
    exact h2.symm
  have : σ ∈ MulAction.stabilizer (Gal(K'/K)) A := by
    have := inv_mem hmem
    simpa using this
  exact (comap_eq_iff_mem_stabilizer A σ).mpr this

/-- **Disjointness of decomposition groups** (CoNF XII (12.1.3)), in the form of the vanishing of
the meet of the two stabilisers. -/
theorem stabilizer_inf_stabilizer_eq_bot_of_ne [IsSepClosure K K']
    {A₁ A₂ : ValuationSubring K'} (hne : A₁ ≠ A₂)
    (h₁ : A₁.comap (algebraMap K K') ≠ ⊤) (h₂ : A₂.comap (algebraMap K K') ≠ ⊤) :
    MulAction.stabilizer (Gal(K'/K)) A₁ ⊓ MulAction.stabilizer (Gal(K'/K)) A₂ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro x hx
  obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.mp hx
  exact eq_one_of_comap_eq_of_comap_eq hne h₁ h₂ x
    ((comap_eq_iff_mem_stabilizer A₁ x).mpr hx₁)
    ((comap_eq_iff_mem_stabilizer A₂ x).mpr hx₂)

/-- **Rigidity of places of the separable closure** (CoNF XII (12.1.4)): an element of
`Gal(K'/K)` commuting with the whole decomposition group of a place `A` over a finite prime `p`
of the number field `K` already lies in that decomposition group. -/
theorem centralizer_stabilizer_valuationSubring_sepClosure {K K' : Type*} [Field K]
    [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    (σ : K' ≃ₐ[K] K')
    (hσ : ∀ τ : K' ≃ₐ[K] K', A.comap (τ : K' →+* K') = A → σ * τ = τ * σ) :
    A.comap (σ : K' →+* K') = A :=
  centralizer_stabilizer_of_disjoint
    (fun _ _ hne h₁ h₂ => stabilizer_inf_stabilizer_eq_bot_of_ne hne h₁ h₂)
    p A hA σ hσ

end Commons.NumberTheory.NumberField.Valuation

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

set_option linter.style.haveILetI false

namespace Commons.FieldTheory.Galois

open scoped Pointwise

/-- **Forward direction, at a single normal intermediate field.**

If `σ` stabilises the valuation subring `A`, then its restriction to any normal intermediate
field `L` stabilises `A ∩ L = A.comap (algebraMap L K')`. -/
theorem restrictNormalHom_smul_comap_eq_of_smul_eq {K K' : Type*} [Field K] [Field K']
    [Algebra K K'] [IsGalois K K'] (A : ValuationSubring K') (σ : K' ≃ₐ[K] K')
    (hσ : σ • A = A) (L : IntermediateField K K') [Normal K L] :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ • (A.comap (algebraMap L K')) =
      A.comap (algebraMap L K') := by
  apply ValuationSubring.ext
  intro x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_comap,
    ValuationSubring.mem_comap]
  have key : σ (algebraMap L K'
        ((AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ)⁻¹ • x)) =
      algebraMap L K' x := by
    change σ (((AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ)⁻¹ • x : L) : K') =
      (x : K')
    rw [← AlgEquiv.restrictNormalHom_apply (F := K) (K₁ := K') L σ
      ((AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ)⁻¹ • x)]
    simp [AlgEquiv.smul_def]
  rw [show (algebraMap L K')
        ((AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ)⁻¹ • x) =
      σ.symm (algebraMap L K' x) by rw [← key]; simp]
  have hmem : σ.symm (algebraMap L K' x) ∈ A ↔ algebraMap L K' x ∈ A := by
    rw [← ValuationSubring.smul_mem_pointwise_smul_iff (g := σ) (S := A)
      (x := σ.symm (algebraMap L K' x)), hσ]
    simp [AlgEquiv.smul_def]
  exact hmem

/-- **Backward direction.** If the restriction of `σ` to every normal intermediate field
stabilises `A ∩ L`, then `σ` stabilises `A`. -/
theorem smul_eq_of_forall_restrictNormalHom_smul_comap_eq {K K' : Type*} [Field K] [Field K']
    [Algebra K K'] [IsGalois K K'] (A : ValuationSubring K') (σ : K' ≃ₐ[K] K')
    (h : ∀ (L : IntermediateField K K') [Normal K L],
      AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ • (A.comap (algebraMap L K')) =
        A.comap (algebraMap L K')) :
    σ • A = A := by
  have key : ∀ x : K', x ∈ A ↔ σ x ∈ A := by
    intro x
    let E : IntermediateField K K' := IntermediateField.adjoin K {x}
    let L : IntermediateField K K' := IntermediateField.normalClosure K E K'
    haveI : Nonempty (E →ₐ[K] K') := ⟨E.val⟩
    haveI : Normal K L := (isNormalClosure_normalClosure K E K').normal
    have hxE : x ∈ E := IntermediateField.mem_adjoin_simple_self K x
    have hxL : x ∈ L := IntermediateField.le_normalClosure E hxE
    have hσxL : σ x ∈ L := by
      have hg : σ x ∈ (σ.toAlgHom.comp E.val).fieldRange := ⟨⟨x, hxE⟩, by simp⟩
      exact AlgHom.fieldRange_le_normalClosure (σ.toAlgHom.comp E.val) hg
    have hL := h L
    have step1 : x ∈ A → σ x ∈ A := by
      intro hxA
      have hxmem : (⟨x, hxL⟩ : L) ∈ A.comap (algebraMap L K') := by
        rw [ValuationSubring.mem_comap]; simpa using hxA
      have hτmem : (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ) (⟨x, hxL⟩ : L) ∈
          A.comap (algebraMap L K') := by
        have hs := ValuationSubring.smul_mem_pointwise_smul
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ) (⟨x, hxL⟩ : L)
          (A.comap (algebraMap L K')) hxmem
        rw [hL] at hs
        simpa [AlgEquiv.smul_def] using hs
      rw [ValuationSubring.mem_comap] at hτmem
      change (((AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ) (⟨x, hxL⟩ : L)) : K') ∈ A
        at hτmem
      rw [AlgEquiv.restrictNormalHom_apply] at hτmem
      simpa using hτmem
    have step2 : σ x ∈ A → x ∈ A := by
      intro hσxA
      have hσxmem : (⟨σ x, hσxL⟩ : L) ∈ A.comap (algebraMap L K') := by
        rw [ValuationSubring.mem_comap]; simpa using hσxA
      have h_eq : (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ) (⟨x, hxL⟩ : L) =
          (⟨σ x, hσxL⟩ : L) := by
        apply Subtype.ext
        simp [AlgEquiv.restrictNormalHom_apply]
      have h2 : (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ)⁻¹ •
            (⟨σ x, hσxL⟩ : L) ∈ A.comap (algebraMap L K') := by
        have hmem : (⟨σ x, hσxL⟩ : L) ∈
            (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ) •
              (A.comap (algebraMap L K')) := by
          rw [hL]; exact hσxmem
        exact (ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
          (g := AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ)
          (S := A.comap (algebraMap L K'))).mp hmem
      have h3 : (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ)⁻¹ •
            (⟨σ x, hσxL⟩ : L) = (⟨x, hxL⟩ : L) := by
        rw [AlgEquiv.smul_def, ← h_eq]
        simp
      rw [h3] at h2
      rw [ValuationSubring.mem_comap] at h2
      simpa using h2
    exact ⟨step1, step2⟩
  apply ValuationSubring.ext
  intro x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have hk := key (σ⁻¹ • x)
  simpa [AlgEquiv.smul_def] using hk

/-- **The stabiliser of a valuation subring of a Galois extension is the intersection of the
stabilisers of its restrictions to the normal intermediate fields.**

Let `K' / K` be a Galois extension (not necessarily finite) and `A` a valuation subring of `K'`.
An element `σ` of `Gal(K'/K) = K' ≃ₐ[K] K'` stabilises `A` if and only if, for every normal
intermediate field `L`, its restriction `σ|_L` stabilises `A ∩ L = A.comap (algebraMap L K')`.

This exhibits the stabiliser as the projective limit of its finite-level counterparts. -/
theorem mem_stabilizer_valuationSubring_iff_forall_restrict {K K' : Type*} [Field K] [Field K']
    [Algebra K K'] [IsGalois K K'] (A : ValuationSubring K') (σ : K' ≃ₐ[K] K') :
    σ ∈ MulAction.stabilizer (K' ≃ₐ[K] K') A ↔
      ∀ (L : IntermediateField K K') [Normal K L],
        AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ ∈
          MulAction.stabilizer (L ≃ₐ[K] L) (A.comap (algebraMap L K')) := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro hσ L hL
    haveI : Normal K L := hL
    rw [MulAction.mem_stabilizer_iff]
    exact restrictNormalHom_smul_comap_eq_of_smul_eq A σ hσ L
  · intro h
    refine smul_eq_of_forall_restrictNormalHom_smul_comap_eq A σ ?_
    intro L hL
    haveI : Normal K L := hL
    exact (MulAction.mem_stabilizer_iff).mp (h L)

end Commons.FieldTheory.Galois
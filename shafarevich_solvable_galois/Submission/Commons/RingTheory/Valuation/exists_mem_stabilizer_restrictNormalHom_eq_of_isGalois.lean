import Mathlib
import Submission.Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq_isGalois
import Submission.Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul
import Submission.Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation

open scoped Pointwise

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The image of a valuation subring under an algebra automorphism is the preimage under the
inverse automorphism. -/
private theorem smul_eq_comap_symm_alg {F K' : Type*} [Field F] [Field K'] [Algebra F K']
    (A : ValuationSubring K') (σ : K' ≃ₐ[F] K') :
    σ • A = A.comap (σ.symm : K' →+* K') := by
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_comap]
  simp [AlgEquiv.smul_def]

/-- **Surjectivity of the restriction map on decomposition groups (general fields).**
Let `E/F` be a Galois algebraic extension, `A` a valuation subring of `E` whose trace on `F` is
proper, and `N/F` a finite normal intermediate field.  Then every `τ : Gal(N/F)` stabilising
`A ∩ N` is the restriction of some `σ : Gal(E/F)` stabilising `A`.

This is the general-field version of `Commons.FieldTheory.Galois.exists_mem_stabilizer_restrictNormalHom_eq`
(which assumes `F` to be a number field).  It follows by lifting `τ` arbitrarily to `σ₀` and
then using the transitivity
`Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq_isGalois` over the base field `↥N` to
correct `σ₀` by an element of `Gal(E/↥N)`. -/
theorem exists_mem_stabilizer_restrictNormalHom_eq_of_isGalois {F E : Type*} [Field F] [Field E]
    [Algebra F E] [IsGalois F E] [Algebra.IsAlgebraic F E] (A : ValuationSubring E)
    (hC : A.comap (algebraMap F E) ≠ ⊤) (N : IntermediateField F E)
    [FiniteDimensional F N] [Normal F N] (τ : ↥N ≃ₐ[F] ↥N)
    (hτ : τ ∈ MulAction.stabilizer (↥N ≃ₐ[F] ↥N) (A.comap (algebraMap ↥N E))) :
    ∃ σ : E ≃ₐ[F] E, σ ∈ MulAction.stabilizer (E ≃ₐ[F] E) A ∧
      AlgEquiv.restrictNormalHom (F := F) (K₁ := E) N σ = τ := by
  -- The trace of `A` on `N` is proper, since otherwise `A` itself (being algebraic over `N`)
  -- would be everything, contradicting the properness of the trace of `A` on `F`.
  have hALne : A.comap (algebraMap ↥N E) ≠ ⊤ := by
    intro h
    refine hC ?_
    have hAtop : A = ⊤ :=
      Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top
        A (F := ↥N) (K' := E) inferInstance h
    rw [hAtop]
    ext x
    simp [ValuationSubring.mem_comap]
  have hτ' : τ • (A.comap (algebraMap ↥N E)) = A.comap (algebraMap ↥N E) :=
    (MulAction.mem_stabilizer_iff).mp hτ
  -- Lift `τ` arbitrarily to an `F`-automorphism `σ₀` of `E`.
  obtain ⟨σ₀, hσ₀⟩ :=
    AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := N) (E := E) τ
  set B : ValuationSubring E := σ₀ • A with hB
  -- `B` has the same trace on `N` as `A`, because `σ₀` restricts to `τ` and `τ` stabilises it.
  have hBcomap : B.comap (algebraMap ↥N E) = A.comap (algebraMap ↥N E) := by
    rw [hB, Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul A σ₀ N, hσ₀, hτ']
  have hBne : B.comap (algebraMap ↥N E) ≠ ⊤ := by rw [hBcomap]; exact hALne
  -- Transitivity over the base field `↥N`: some `σ' : E ≃ₐ[↥N] E` carries `B` back onto `A`.
  obtain ⟨σ', hσ'⟩ :=
    exists_smul_eq_of_comap_eq_isGalois (F := ↥N) (E := E) B A hBcomap hBne
  -- `σ'` fixes `N`, hence (viewed over `F`) restricts to the identity of `Gal(N/F)`.
  have hfix : AlgEquiv.restrictNormalHom (F := F) (K₁ := E) N (σ'.restrictScalars F) = 1 := by
    rw [show AlgEquiv.restrictNormalHom (F := F) (K₁ := E) N (σ'.restrictScalars F) =
        (σ'.restrictScalars F).restrictNormal N from rfl]
    ext x
    rw [AlgEquiv.restrictNormal_apply, AlgEquiv.restrictScalars_apply]
    show σ' ↑x = ↑x
    exact σ'.commutes x
  -- Passing to the `F`-linear scalar restriction does not change the action on `B`.
  have hsmul : (σ'.restrictScalars F) • B = σ' • B := by
    rw [smul_eq_comap_symm_alg B (σ'.restrictScalars F), smul_eq_comap_symm_alg B σ']
    congr 1
  refine ⟨(σ'.restrictScalars F) * σ₀, ?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff, mul_smul, ← hB, hsmul, hσ']
  · rw [map_mul, hfix, hσ₀, one_mul]

end Commons.RingTheory.Valuation

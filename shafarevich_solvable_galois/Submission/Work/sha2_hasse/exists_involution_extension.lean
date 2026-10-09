import Mathlib
import Submission.Work.SSGRoute.sha2_hasse.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Extending the local complex conjugation to an involution of `G_k`

Let `k` be a number field, `L` a finite Galois level of `k̄/k` and `v` an infinite place of `L`.
An automorphism `σ₀` of `L` over `k` which acts by complex conjugation with respect to
`v.embedding` extends to an involution `σ` of `Gal(k̄/k)` with `levelRes L σ = σ₀`, together with a
ring homomorphism `φ : k̄ →+* ℂ` extending `v.embedding` and intertwining `σ` with complex
conjugation.

The construction: embed `k̄` into `ℂ` by a ring homomorphism `φ` extending `v.embedding`
(`ComplexEmbedding.lift`), and let `σ := φ⁻¹ ∘ conj ∘ φ`. Since `v.embedding` restricted to `k` is
real-valued (`hconj` evaluated on `k`), complex conjugation preserves the image `φ(k̄)`, so the two
`k`-embeddings `φ` and `conj ∘ φ` of `k̄` into `ℂ` differ by an element of `Gal(k̄/k)`
(`ComplexEmbedding.exists_comp_symm_eq_of_comp_eq`); this element is the desired involution.
-/

set_option autoImplicit false

open NumberField

namespace Work.sha2_hasse

theorem exists_involution_extension
    {k : Type} [Field k] [NumberField k]
    (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (v : NumberField.InfinitePlace (Work.SSGRoute.sha2_hasse.Lf L))
    (σ₀ : Work.SSGRoute.sha2_hasse.Lf L ≃ₐ[k] Work.SSGRoute.sha2_hasse.Lf L)
    (hconj : ∀ x : Work.SSGRoute.sha2_hasse.Lf L,
      NumberField.InfinitePlace.embedding v (σ₀ x) = starRingEnd ℂ (NumberField.InfinitePlace.embedding v x)) :
    ∃ (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (φ : AlgebraicClosure k →+* ℂ),
      σ ^ 2 = 1 ∧ Work.SSGRoute.sha2_hasse.levelRes L σ = σ₀ ∧
      (∀ x : Work.SSGRoute.sha2_hasse.Lf L,
        φ (algebraMap (Work.SSGRoute.sha2_hasse.Lf L) (AlgebraicClosure k) x) =
          NumberField.InfinitePlace.embedding v x) ∧
      (∀ x : AlgebraicClosure k, φ (σ x) = starRingEnd ℂ (φ x)) := by
  let E := Work.SSGRoute.sha2_hasse.Lf L
  -- A `k̄`-embedding `φ` extending the local embedding `v.embedding` of `L`.
  let φ : AlgebraicClosure k →+* ℂ :=
    ComplexEmbedding.lift (AlgebraicClosure k) (NumberField.InfinitePlace.embedding v)
  have hφ : ∀ y : E, φ (algebraMap E (AlgebraicClosure k) y)
      = NumberField.InfinitePlace.embedding v y :=
    fun y => ComplexEmbedding.lift_algebraMap_apply (AlgebraicClosure k)
      (NumberField.InfinitePlace.embedding v) y
  have hφc : ∀ y : E, φ (y : AlgebraicClosure k) = NumberField.InfinitePlace.embedding v y := by
    intro y
    rw [← IntermediateField.algebraMap_apply (L : IntermediateField k (AlgebraicClosure k)) y]
    exact hφ y
  -- `φ` is real on `k`: on `k ⊆ L` the hypothesis `hconj` forces `v.embedding` to be fixed by
  -- complex conjugation.
  have hreal : ComplexEmbedding.IsReal (φ.comp (algebraMap k (AlgebraicClosure k))) := by
    rw [ComplexEmbedding.isReal_iff]
    rw [← ComplexEmbedding.conjugate_comp]
    ext a
    simp only [RingHom.comp_apply]
    rw [ComplexEmbedding.conjugate_coe_eq]
    have h1 : φ (algebraMap k (AlgebraicClosure k) a)
        = NumberField.InfinitePlace.embedding v (algebraMap k E a) := by
      rw [IsScalarTower.algebraMap_apply k E (AlgebraicClosure k)]
      exact hφ _
    rw [h1]
    have hc := hconj (algebraMap k E a)
    rw [AlgEquiv.commutes] at hc
    exact hc.symm
  -- `φ` and `conj ∘ φ` are two `k`-embeddings of `k̄` into `ℂ`, so they differ by an element of
  -- `Gal(k̄/k)`, which is the desired involution.
  obtain ⟨σ₁, hσ₁⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq
      (K := AlgebraicClosure k) (k := k) φ (ComplexEmbedding.conjugate φ) (by
        rw [ComplexEmbedding.conjugate_comp]; exact hreal.symm)
  let σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k := σ₁.symm
  have hσ : φ.comp (↑σ : AlgebraicClosure k →+* AlgebraicClosure k)
      = ComplexEmbedding.conjugate φ := hσ₁
  have hIsConj : ComplexEmbedding.IsConj φ σ := hσ.symm
  refine ⟨σ, φ, ?_, ?_, hφ, ?_⟩
  · -- `σ` is an involution, because `φ ∘ σ = conj ∘ φ` and `conj² = 1`.
    rw [pow_two]
    ext x
    rw [AlgEquiv.mul_apply, AlgEquiv.one_apply]
    exact NumberField.ComplexEmbedding.isConj_apply_apply hIsConj x
  · -- `σ` restricts to `σ₀` on `L`.
    ext x
    rw [Work.SSGRoute.sha2_hasse.levelRes_apply]
    apply φ.injective
    have hcong := RingHom.congr_fun hσ (x : AlgebraicClosure k)
    simp only [RingHom.comp_apply] at hcong
    change φ ((↑σ : AlgebraicClosure k →+* AlgebraicClosure k) (x : AlgebraicClosure k))
      = φ ((σ₀ x : E) : AlgebraicClosure k)
    rw [hcong, ComplexEmbedding.conjugate_coe_eq, hφc x, hφc (σ₀ x)]
    exact (hconj x).symm
  · -- `φ` intertwines `σ` with complex conjugation.
    intro x
    exact (NumberField.ComplexEmbedding.IsConj.eq hIsConj x).trans
      (starRingEnd_apply (φ x)).symm

end Work.sha2_hasse

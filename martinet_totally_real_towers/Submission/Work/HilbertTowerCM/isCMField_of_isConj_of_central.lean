import Mathlib

/-!
# A totally complex Galois number field with a *central* conjugation is CM

Let `L/ℚ` be a totally complex Galois number field.  Mathlib's
`NumberField.IsCMField.of_forall_isConj` says that `L` is CM as soon as some
`σ ∈ Gal(L/ℚ)` is the complex conjugation *at every* complex embedding of `L`
(`ComplexEmbedding.IsConj φ σ` for all `φ : L →+* ℂ`).

We need the version in which `σ` is only known to be the conjugation at **one**
embedding, compensated by the hypothesis that `σ` is **central** in `Gal(L/ℚ)`.
Centrality is exactly what is used: for any other embedding `ψ`, normality of `L/ℚ`
gives `ψ = φ.comp ν.symm` for some `ν : Gal(L/ℚ)`, and

`IsConj φ σ  ⟹  IsConj (φ.comp ν.symm) (ν.symm⁻¹ * σ * ν.symm) = IsConj ψ σ`,

the last equality because `σ` commutes with `ν.symm`.  (For abelian `L/ℚ` this is
Mathlib's `NumberField.IsCMField.of_isAbelianGalois`, which is the special case in
which every element is central; that proof is what is adapted here.)

The use in the CM endgame of the Martinet tower: the Galois groups of the levels are
non-abelian in general, but the complex conjugation of an unramified level over a
totally complex base is central, and this lemma turns that into CM-ness of the level.
-/

open NumberField ComplexEmbedding

namespace Work.HilbertTowerCM

theorem isCMField_of_isConj_of_central (L : Type*) [Field L] [NumberField L]
    [NumberField.IsTotallyComplex L] [IsGalois ℚ L] (σ : L ≃ₐ[ℚ] L)
    (hc : ∀ ρ : L ≃ₐ[ℚ] L, σ * ρ = ρ * σ) (φ : L →+* ℂ)
    (hφ : NumberField.ComplexEmbedding.IsConj φ σ) : NumberField.IsCMField L := by
  -- Every embedding of the *normal* field `L` is `φ` composed with an element of
  -- `Gal(L/ℚ)`, and centrality of `σ` transports `IsConj φ σ` to that embedding.
  have hσ : ∀ ψ : L →+* ℂ, NumberField.ComplexEmbedding.IsConj ψ σ := by
    intro ψ
    obtain ⟨ν, rfl⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) φ ψ
      (by ext q; simp)
    have hcomm : ν.symm⁻¹ * σ * ν.symm = σ := by
      rw [mul_assoc, hc ν.symm, ← mul_assoc, inv_mul_cancel, one_mul]
    have := hφ.comp ν.symm
    rwa [hcomm] at this
  exact NumberField.IsCMField.of_forall_isConj (K := L) (σ := σ) hσ

end Work.HilbertTowerCM

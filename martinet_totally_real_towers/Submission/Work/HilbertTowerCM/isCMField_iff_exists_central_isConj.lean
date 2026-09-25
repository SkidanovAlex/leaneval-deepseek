import Mathlib
import Submission.Work.HilbertTowerCM.isCMField_of_isConj_of_central
import Submission.Work.HilbertTowerCM.finrank_realPart_eq_card_conj

/-!
# CM-ness of a totally complex Galois number field is *exactly* centrality of a conjugation

Let `L/ℚ` be a totally complex Galois number field.  This module proves the equivalence

`L` is CM  ↔  there is a `σ ∈ Gal(L/ℚ)` which is **central** and is the complex
conjugation at (at least) **one** embedding of `L`.

The forward implication is the classical fact that complex conjugation is a central element of
the Galois group of a Galois extension of `ℚ`: `L` being CM supplies a conjugation
`c = NumberField.IsCMField.complexConj L ∈ Gal(L/L⁺)`, which is a `ℚ`-automorphism of `L` and is
the conjugation at *every* embedding of `L`; the same is then true of `ρ c ρ⁻¹` for every
`ρ ∈ Gal(L/ℚ)`, so uniqueness of the conjugation at a fixed embedding
(`ComplexEmbedding.IsConj.ext`) gives `ρ c ρ⁻¹ = c`, i.e. centrality.

The backward implication is `Work.HilbertTowerCM.isCMField_of_isConj_of_central`: a central
element which is the conjugation at one embedding is the conjugation at every embedding, so
`NumberField.IsCMField.of_forall_isConj` applies.

Together they say that the *only* obstruction to an unramified Galois level of the Hilbert class
tower over a CM base being CM is the non-centrality of the lift of complex conjugation; cf.
`Submission/Work/HilbertTowerCM/README.md`.
-/

open NumberField ComplexEmbedding

namespace Work.HilbertTowerCM

theorem isCMField_iff_exists_central_isConj (L : Type*) [Field L] [NumberField L]
    [NumberField.IsTotallyComplex L] [IsGalois ℚ L] :
    NumberField.IsCMField L ↔
      ∃ σ : L ≃ₐ[ℚ] L, (∀ ρ : L ≃ₐ[ℚ] L, σ * ρ = ρ * σ) ∧
        ∃ φ : L →+* ℂ, NumberField.ComplexEmbedding.IsConj φ σ := by
  refine ⟨fun h => ?_, fun ⟨σ, hc, φ, hφ⟩ =>
    isCMField_of_isConj_of_central L σ hc φ hφ⟩
  -- The complex conjugation of the CM field `L`, viewed as a `ℚ`-automorphism of `L`.
  let σ : L ≃ₐ[ℚ] L := (NumberField.IsCMField.complexConj L).restrictScalars ℚ
  -- It is the conjugation at *every* embedding of `L`.
  have hσ : ∀ φ : L →+* ℂ, NumberField.ComplexEmbedding.IsConj φ σ := fun φ =>
    NumberField.IsCMField.isConj_complexConj L φ
  refine ⟨σ, ?_, ?_⟩
  · -- centrality: `ρ * σ * ρ⁻¹` is again the conjugation at `φ.comp ρ`, and the conjugation at a
    -- fixed embedding is unique.
    intro ρ
    have hcent : σ = ρ⁻¹ * σ * ρ :=
      ComplexEmbedding.IsConj.ext
        (hσ ((Classical.choice (inferInstance : Nonempty (L →+* ℂ))).comp ρ))
        ((hσ (Classical.choice (inferInstance : Nonempty (L →+* ℂ)))).comp ρ)
    have h2 : ρ * σ = σ * ρ := by
      conv_lhs => rw [hcent]
      group
    exact h2.symm
  · exact ⟨Classical.choice (inferInstance : Nonempty (L →+* ℂ)), hσ _⟩

end Work.HilbertTowerCM

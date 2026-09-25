import Mathlib

/-!
# Complex conjugation on a Galois number field is induced by an automorphism

For a number field `L` that is Galois over `ℚ`, every complex embedding `φ : L →+* ℂ` has a
conjugate `φ̄ = star φ` which is again an embedding of `L`.  Since `L/ℚ` is normal and `Galois`
in Mathlib's sense, this conjugate embedding is obtained by precomposition with an element of
`Gal(L/ℚ)`:

`∃ σ : L ≃ₐ[ℚ] L, IsConj φ σ`,  i.e.  `conjugate φ = φ.comp σ`.

The point is Mathlib's `ComplexEmbedding.exists_comp_symm_eq_of_comp_eq`, applied to the pair
`(φ, conjugate φ)`: both restrict to the same map on `ℚ` (complex conjugation fixes `ℚ`
pointwise), so they differ by an element of the Galois group.
-/

namespace Work.HilbertTowerCM

/-- **The complex conjugation of a Galois number field is induced by a `ℚ`-automorphism.**
For `L/ℚ` Galois and any complex embedding `φ` of `L`, there is `σ : L ≃ₐ[ℚ] L` with
`IsConj φ σ`, i.e. `conjugate φ = φ.comp σ`. -/
theorem exists_isConj_of_isGalois (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (φ : L →+* ℂ) : ∃ σ : L ≃ₐ[ℚ] L, NumberField.ComplexEmbedding.IsConj φ σ := by
  -- `φ` and its complex conjugate `conjugate φ` agree on `ℚ`, hence differ by an element of
  -- the Galois group: `φ.comp σ.symm = conjugate φ` for some `σ : Gal(L/ℚ)`.
  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) φ
    (NumberField.ComplexEmbedding.conjugate φ) (by ext q; simp)
  exact ⟨σ.symm, hσ.symm⟩

end Work.HilbertTowerCM

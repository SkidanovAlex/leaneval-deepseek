import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- **Discriminant vs. conjugate size.**  If every conjugate of every element of a family
`b : Fin d → F` (a number field) is bounded by `M ≥ 0`, then `|discr ℚ b| ≤ (d! · M^d)²`.

Via `Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two` (the discriminant of a family is the
square of the determinant of the matrix `(σ (b i))`, `σ : F →ₐ[ℚ] ℂ`, after identifying the index
type with the embeddings via any bijection — available since `Fintype.card (F →ₐ[ℚ] ℂ) = d`), and
the Leibniz-formula bound `Matrix.det_le` for the complex absolute value. -/
theorem discr_le_of_embeddings_bound {F : Type*} [Field F] [NumberField F]
    (b : Fin (Module.finrank ℚ F) → F) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ (i : Fin (Module.finrank ℚ F)) (σ : F →ₐ[ℚ] ℂ), ‖σ (b i)‖ ≤ M) :
    |((Algebra.discr ℚ b : ℚ) : ℝ)| ≤
      (((Module.finrank ℚ F).factorial : ℝ) * M ^ (Module.finrank ℚ F)) ^ 2 := by
  classical
  -- Identify `Fin d` with the set of embeddings of `F` in `ℂ`.
  let e : Fin (Module.finrank ℚ F) ≃ (F →ₐ[ℚ] ℂ) :=
    (Fintype.equivFinOfCardEq (AlgHom.card ℚ F ℂ)).symm
  -- The discriminant is the square of the determinant of the embedding matrix.
  have hdisc := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ b e
  -- Every entry of that matrix is a conjugate, hence bounded by `M` in absolute value.
  have hent : ∀ i j, ‖(Algebra.embeddingsMatrixReindex ℚ ℂ b e) i j‖ ≤ M := by
    intro i j
    rw [Algebra.embeddingsMatrixReindex, Matrix.reindex_apply, Matrix.submatrix_apply,
      Algebra.embeddingsMatrix_apply]
    exact hb i _
  -- Leibniz-formula bound for the determinant.
  have hdet := Matrix.det_le (A := Algebra.embeddingsMatrixReindex ℚ ℂ b e)
      (abv := IsAbsoluteValue.toAbsoluteValue (fun z : ℂ => ‖z‖)) (x := M) hent
  simp only [Fintype.card_fin, IsAbsoluteValue.toAbsoluteValue_apply, nsmul_eq_mul] at hdet
  -- Compare norms in the discriminant identity.
  have hnorm : ‖(algebraMap ℚ ℂ) (Algebra.discr ℚ b)‖
      = ‖(Algebra.embeddingsMatrixReindex ℚ ℂ b e).det‖ ^ 2 := by
    rw [hdisc, norm_pow]
  have hma : (algebraMap ℚ ℂ) (Algebra.discr ℚ b) = ((Algebra.discr ℚ b : ℚ) : ℂ) := rfl
  rw [hma, Complex.norm_ratCast] at hnorm
  rw [hnorm]
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact hdet

end Work.BW

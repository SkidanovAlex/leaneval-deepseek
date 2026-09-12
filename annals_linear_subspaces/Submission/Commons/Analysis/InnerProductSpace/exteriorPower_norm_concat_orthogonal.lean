import Mathlib.Analysis.InnerProductSpace.ExteriorPower

namespace Commons.Analysis.InnerProductSpace

open Matrix exteriorPower

noncomputable section

/-- The Gram matrix of an `Fin.append` of two pairwise-orthogonal families is the
block-diagonal matrix formed from the two Gram matrices (after reindexing rows and
columns by `Fin p ⊕ Fin q ≃ Fin (p + q)`). -/
lemma gram_append_orthogonal_block {p q : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u : Fin p → E) (v : Fin q → E)
    (horth : ∀ i : Fin p, ∀ j : Fin q, inner ℝ (u i) (v j) = 0) :
    (Matrix.gram ℝ (Fin.append u v)).submatrix (finSumFinEquiv : Fin p ⊕ Fin q → Fin (p + q))
        (finSumFinEquiv : Fin p ⊕ Fin q → Fin (p + q)) =
      Matrix.fromBlocks (Matrix.gram ℝ u) 0 0 (Matrix.gram ℝ v) := by
  classical
  ext a b
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      simp [Matrix.gram_apply, finSumFinEquiv_apply_left]
    | inr j =>
      simp [Matrix.gram_apply]
      exact horth i j
  | inr i =>
    cases b with
    | inl j =>
      simp [Matrix.gram_apply, real_inner_comm]
      exact horth j i
    | inr j =>
      simp [Matrix.gram_apply]

lemma exteriorPower_norm_concat_orthogonal {p q : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (u : Fin p → E) (v : Fin q → E)
    (horth : ∀ i : Fin p, ∀ j : Fin q, inner ℝ (u i) (v j) = 0) :
    ‖exteriorPower.ιMulti ℝ (p + q) (Fin.append u v)‖ =
      ‖exteriorPower.ιMulti ℝ p u‖ * ‖exteriorPower.ιMulti ℝ q v‖ := by
  classical
  have hdet : (Matrix.gram ℝ (Fin.append u v)).det =
      (Matrix.gram ℝ u).det * (Matrix.gram ℝ v).det := by
    calc
      (Matrix.gram ℝ (Fin.append u v)).det
          = ((Matrix.gram ℝ (Fin.append u v)).submatrix
                (finSumFinEquiv : Fin p ⊕ Fin q → Fin (p + q))
                (finSumFinEquiv : Fin p ⊕ Fin q → Fin (p + q))).det := by
              rw [Matrix.det_submatrix_equiv_self]
      _ = (Matrix.fromBlocks (Matrix.gram ℝ u) 0 0 (Matrix.gram ℝ v)).det := by
              rw [gram_append_orthogonal_block u v horth]
      _ = (Matrix.gram ℝ u).det * (Matrix.gram ℝ v).det := by
              exact Matrix.det_fromBlocks_zero₁₂ (Matrix.gram ℝ u)
                (0 : Matrix (Fin q) (Fin p) ℝ) (Matrix.gram ℝ v)
  have hsq_append : ‖exteriorPower.ιMulti ℝ (p + q) (Fin.append u v)‖ ^ 2 =
      (Matrix.gram ℝ (Fin.append u v)).det := by
    calc
      ‖exteriorPower.ιMulti ℝ (p + q) (Fin.append u v)‖ ^ 2
          = inner ℝ (exteriorPower.ιMulti ℝ (p + q) (Fin.append u v))
              (exteriorPower.ιMulti ℝ (p + q) (Fin.append u v)) := by
            exact (inner_self_eq_norm_sq_to_K (𝕜 := ℝ)
              (exteriorPower.ιMulti ℝ (p + q) (Fin.append u v))).symm
      _ = (Matrix.gram ℝ (Fin.append u v)).det := by
            exact exteriorPower.inner_ιMulti_self (Fin.append u v)
  have hsq_u : ‖exteriorPower.ιMulti ℝ p u‖ ^ 2 = (Matrix.gram ℝ u).det := by
    calc
      ‖exteriorPower.ιMulti ℝ p u‖ ^ 2
          = inner ℝ (exteriorPower.ιMulti ℝ p u) (exteriorPower.ιMulti ℝ p u) := by
            exact (inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (exteriorPower.ιMulti ℝ p u)).symm
      _ = (Matrix.gram ℝ u).det := by
            exact exteriorPower.inner_ιMulti_self u
  have hsq_v : ‖exteriorPower.ιMulti ℝ q v‖ ^ 2 = (Matrix.gram ℝ v).det := by
    calc
      ‖exteriorPower.ιMulti ℝ q v‖ ^ 2
          = inner ℝ (exteriorPower.ιMulti ℝ q v) (exteriorPower.ιMulti ℝ q v) := by
            exact (inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (exteriorPower.ιMulti ℝ q v)).symm
      _ = (Matrix.gram ℝ v).det := by
            exact exteriorPower.inner_ιMulti_self v
  have hsq : ‖exteriorPower.ιMulti ℝ (p + q) (Fin.append u v)‖ ^ 2 =
      (‖exteriorPower.ιMulti ℝ p u‖ * ‖exteriorPower.ιMulti ℝ q v‖) ^ 2 := by
    calc
      ‖exteriorPower.ιMulti ℝ (p + q) (Fin.append u v)‖ ^ 2
          = (Matrix.gram ℝ (Fin.append u v)).det := hsq_append
      _ = (Matrix.gram ℝ u).det * (Matrix.gram ℝ v).det := hdet
      _ = ‖exteriorPower.ιMulti ℝ p u‖ ^ 2 * ‖exteriorPower.ιMulti ℝ q v‖ ^ 2 := by
            rw [hsq_u, hsq_v]
      _ = (‖exteriorPower.ιMulti ℝ p u‖ * ‖exteriorPower.ιMulti ℝ q v‖) ^ 2 := by ring
  have hnonneg1 : 0 ≤ ‖exteriorPower.ιMulti ℝ (p + q) (Fin.append u v)‖ := norm_nonneg _
  have hnonneg2 : 0 ≤ ‖exteriorPower.ιMulti ℝ p u‖ * ‖exteriorPower.ιMulti ℝ q v‖ := by
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h | h
  · exact h
  · linarith

end

end Commons.Analysis.InnerProductSpace
import Submission.Defs
import Mathlib.Analysis.InnerProductSpace.GramMatrix

open EquiangularLinesFixedAngle
open Filter
open scoped RealInnerProductSpace

namespace Submission

/-- The graph on the index set of an equiangular family whose edges are the pairs with
negative inner product `-α`. -/
def assocGraph (α : ℝ) {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d)) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ ⟪v i, v j⟫ = -α
  symm := ⟨by
    intro i j h
    rcases h with ⟨hij, hval⟩
    exact ⟨hij.symm, by simpa [real_inner_comm] using hval⟩⟩
  loopless := ⟨by
    intro i h
    exact h.1 rfl⟩

lemma mem_assocGraph_iff (α : ℝ) {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d)) {i j : Fin n} :
    (assocGraph α v).Adj i j ↔ i ≠ j ∧ ⟪v i, v j⟫ = -α := Iff.rfl

/-- `(2α)(λ+1/2) = 1`. -/
lemma two_mul_lam_add_half {α : ℝ} (hα : α ≠ 0) : 2 * α * (lam α + 1 / 2) = 1 := by
  calc
    2 * α * (lam α + 1 / 2) = 2 * α * lam α + 2 * α * (1 / 2) := by ring
    _ = (1 - α) + α := by rw [two_mul_lam hα]; ring
    _ = 1 := by ring

/-- Entry formula for the diagonal. -/
lemma graphMatrix_diag (α : ℝ) {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n) :
    graphMatrix α G i i = lam α + 1 / 2 := by
  classical
  simp [graphMatrix]

/-- Entry formula for off-diagonal entries. -/
lemma graphMatrix_offdiag_of_adj (α : ℝ) {n : ℕ} (G : SimpleGraph (Fin n)) {i j : Fin n}
    (hij : i ≠ j) (hG : G.Adj i j) : graphMatrix α G i j = -(1/2) := by
  classical
  simp [graphMatrix, hij, hG]

lemma graphMatrix_offdiag_of_not_adj (α : ℝ) {n : ℕ} (G : SimpleGraph (Fin n)) {i j : Fin n}
    (hij : i ≠ j) (hG : ¬ G.Adj i j) : graphMatrix α G i j = 1/2 := by
  classical
  simp [graphMatrix, hij, hG]

/-- Entrywise: the Gram matrix of an equiangular family equals `2α M`. -/
lemma gram_apply_eq_two_mul_graphMatrix (α : ℝ) {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hα0 : 0 < α)
    (hvnorm : ∀ i, ‖v i‖ = 1)
    (hvangle : ∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v i, v j⟫| = α) (i j : Fin n) :
    (Matrix.gram ℝ v) i j = (2 * α) * graphMatrix α (assocGraph α v) i j := by
  classical
  have hαz : α ≠ 0 := ne_of_gt hα0
  by_cases hij : i = j
  · subst j
    rw [Matrix.gram_apply, real_inner_self_eq_norm_sq, hvnorm i, graphMatrix_diag]
    rw [two_mul_lam_add_half hαz]
    norm_num
  · have h := hvangle hij
    have hval : ⟪v i, v j⟫ = α ∨ ⟪v i, v j⟫ = -α := eq_or_eq_neg_of_abs_eq h
    rcases hval with hpos | hneg
    · rw [Matrix.gram_apply, hpos]
      rw [graphMatrix_offdiag_of_not_adj α _ hij]
      · ring
      · intro hadj
        have hnegval : ⟪v i, v j⟫ = -α := (mem_assocGraph_iff α v).mp hadj |>.2
        linarith
    · rw [Matrix.gram_apply, hneg]
      rw [graphMatrix_offdiag_of_adj α _ hij (by exact ⟨hij, hneg⟩)]
      ring

/-- The Gram matrix of an equiangular family equals `2α M`. -/
lemma gram_eq_two_mul_graphMatrix (α : ℝ) {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hα0 : 0 < α)
    (hvnorm : ∀ i, ‖v i‖ = 1)
    (hvangle : ∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v i, v j⟫| = α) :
    Matrix.gram ℝ v = (2 * α) • graphMatrix α (assocGraph α v) := by
  classical
  apply Matrix.ext
  intro i j
  rw [gram_apply_eq_two_mul_graphMatrix α v hα0 hvnorm hvangle i j]
  simp [smul_eq_mul]

end Submission

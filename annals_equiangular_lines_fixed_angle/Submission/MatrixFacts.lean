import Submission.Correspondence

open EquiangularLinesFixedAngle
open Filter
open Matrix
open scoped RealInnerProductSpace

namespace Submission

/-! Facts linking equiangular line configurations to the positive-semidefinite matrix
`M = λ I - A_G + ½ J` of rank at most `d`. -/

/-- Coordinate formula for the real inner product on `EuclideanSpace ℝ (Fin d)`. -/
lemma euclidean_inner_apply {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) :
    ⟪x, y⟫ = ∑ i : Fin d, x i * y i := by
  rw [PiLp.inner_apply]
  simp [mul_comm]

/-- The Gram matrix of vectors in `𝔼^d` has rank at most `d`. -/
lemma rank_gram_le {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d)) :
    (Matrix.gram ℝ v).rank ≤ d := by
  classical
  let A : Matrix (Fin n) (Fin d) ℝ := fun i k => (v i) k
  have hfac : Matrix.gram ℝ v = A * Aᵀ := by
    ext i j
    rw [Matrix.gram_apply, euclidean_inner_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro x hx
    simp [A, Matrix.transpose]
  rw [hfac]
  have hsym : Aᵀ = Aᴴ := by
    ext i j; rfl
  rw [hsym]
  rw [Matrix.rank_self_mul_conjTranspose]
  exact Matrix.rank_le_width A

/-- Scalar multiplication does not increase the rank. -/
lemma rank_smul_le {n : ℕ} (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    (c • A).rank ≤ A.rank := by
  classical
  rw [Matrix.rank, Matrix.rank]
  apply Submodule.finrank_mono
  have hmul : (c • A).mulVecLin = c • A.mulVecLin := by
    simp [Matrix.mulVecLin, (Matrix.mulVecBilin ℝ ℝ).map_smul]
  rw [hmul]
  intro y hy
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hy
  refine LinearMap.mem_range.mpr ⟨c • x, ?_⟩
  calc
    A.mulVecLin (c • x) = c • A.mulVecLin x := A.mulVecLin.map_smul c x
    _ = (c • A.mulVecLin) x := by simp [LinearMap.smul_apply]
    _ = y := hx

/-- From `gram v = 2α M` we recover `M = (2α)⁻¹ • gram v`. -/
lemma graphMatrix_eq_inv_smul_gram {α : ℝ} {n d : ℕ}
    (v : Fin n → EuclideanSpace ℝ (Fin d)) (hαz : α ≠ 0)
    (hgram : Matrix.gram ℝ v = (2 * α) • graphMatrix α (assocGraph α v)) :
    graphMatrix α (assocGraph α v) = (2 * α)⁻¹ • Matrix.gram ℝ v := by
  calc
    graphMatrix α (assocGraph α v)
        = (2 * α)⁻¹ • ((2 * α) • graphMatrix α (assocGraph α v)) := by
          rw [smul_smul]
          have h : (2 * α)⁻¹ * (2 * α) = 1 := by field_simp [hαz]
          rw [h]
          simp
    _ = (2 * α)⁻¹ • Matrix.gram ℝ v := by rw [← hgram]

/-- If a Gram matrix equals `2α M`, then `M` has rank at most that of the Gram matrix. -/
lemma rank_graphMatrix_le_of_gram_eq {α : ℝ} {n d : ℕ}
    (v : Fin n → EuclideanSpace ℝ (Fin d)) (hα0 : 0 < α)
    (hgram : Matrix.gram ℝ v = (2 * α) • graphMatrix α (assocGraph α v)) :
    (graphMatrix α (assocGraph α v)).rank ≤ d := by
  classical
  have hαz : α ≠ 0 := ne_of_gt hα0
  rw [graphMatrix_eq_inv_smul_gram v hαz hgram]
  exact le_trans (rank_smul_le (2 * α)⁻¹ (Matrix.gram ℝ v)) (rank_gram_le v)

/-- For an equiangular configuration, the matrix `M = λI - A_G + ½J` has rank at most `d`. -/
lemma rank_graphMatrix_le {α : ℝ} {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hα0 : 0 < α)
    (hvnorm : ∀ i, ‖v i‖ = 1)
    (hvangle : ∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v i, v j⟫| = α) :
    (graphMatrix α (assocGraph α v)).rank ≤ d := by
  exact rank_graphMatrix_le_of_gram_eq v hα0 (gram_eq_two_mul_graphMatrix α v hα0 hvnorm hvangle)

/-- For an equiangular configuration, the matrix `M = λI - A_G + ½J` is positive semidefinite. -/
lemma graphMatrix_posSemidef_of_config {α : ℝ} {n d : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hα0 : 0 < α)
    (hvnorm : ∀ i, ‖v i‖ = 1)
    (hvangle : ∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v i, v j⟫| = α) :
    (graphMatrix α (assocGraph α v)).PosSemidef := by
  classical
  have hαz : α ≠ 0 := ne_of_gt hα0
  rw [graphMatrix_eq_inv_smul_gram v hαz (gram_eq_two_mul_graphMatrix α v hα0 hvnorm hvangle)]
  exact (Matrix.posSemidef_gram ℝ v).smul (by positivity)

end Submission

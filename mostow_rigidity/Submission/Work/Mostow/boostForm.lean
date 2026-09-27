import Mathlib
import Submission.Work.Mostow.poCenterDefs

/-!
# The hyperbolic boostMat_poCenterDefs preserves the form `J = pmOneMat`

`boostMat_poCenterDefs i c s` (`c ^ 2 - s ^ 2 = 1`, `poCenterDefs`) is the hyperbolic boostMat_poCenterDefs mixing the spatial
coordinate `i` with the time coordinate.  This file proves `boostForm`: the boostMat_poCenterDefs matrix `B`
satisfies `Bᵀ J B = J` and `B J Bᵀ = J`, where `J = pmOneMat = diag(1,…,1,−1)`.

Since `B` is symmetric (`boost_transpose`), the two statements are the same matrix identity
`B J B = J`; it is proved blockwise, using the four `n × n` / `n × 1` / `1 × n` / `1 × 1` block
identities for the boostMat_poCenterDefs:

* `B₁₁ B₁₁ - B₁₂ B₂₁ = 1`  (uses `c ^ 2 - s ^ 2 = 1`),
* `B₁₁ B₁₂ - B₁₂ B₂₂ = 0`,
* `B₂₁ B₁₁ - B₂₂ B₂₁ = 0`,
* `B₂₁ B₁₂ - B₂₂ B₂₂ = -1` (uses `c ^ 2 - s ^ 2 = 1`).
-/

namespace Work.Mostow

open Matrix LeanEval.Geometry.MostowRigidity

noncomputable section

variable {n : ℕ}

/-! ## Block identities for the four blocks of a boostMat_poCenterDefs -/

/-- The `(1,1)` block relation: `B₁₁² − B₁₂B₂₁ = 1`. -/
lemma boostP_mul_boostP_sub_boostU_mul_boostV (i : Fin n) (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) :
    boostP_poCenterDefs i c * boostP_poCenterDefs i c - boostU i s * boostV i s = 1 := by
  ext p q
  simp only [boostP_poCenterDefs, boostU, boostV, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply,
    Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_one]
  split_ifs <;> simp_all <;> nlinarith

/-- The `(1,2)` block relation: `B₁₁B₁₂ = B₁₂B₂₂`. -/
lemma boostP_mul_boostU_eq_boostU_mul_boostW (i : Fin n) (c s : ℝ) :
    boostP_poCenterDefs i c * boostU i s = boostU i s * boostW c := by
  ext p k
  rw [boostP_poCenterDefs, Matrix.diagonal_mul]
  simp only [boostU, boostW, Matrix.mul_apply, Fin.sum_univ_one]
  split_ifs <;> ring

/-- The `(2,1)` block relation: `B₂₁B₁₁ = B₂₂B₂₁`. -/
lemma boostV_mul_boostP_eq_boostW_mul_boostV (i : Fin n) (c s : ℝ) :
    boostV i s * boostP_poCenterDefs i c = boostW c * boostV i s := by
  ext k p
  rw [boostP_poCenterDefs, Matrix.mul_diagonal]
  simp only [boostV, boostW, Matrix.mul_apply, Fin.sum_univ_one]
  split_ifs <;> ring

/-- The `(2,2)` block relation: `B₂₁B₁₂ − B₂₂² = −1`. -/
lemma boostV_mul_boostU_sub_boostW_mul_boostW (i : Fin n) (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) :
    boostV i s * boostU i s - boostW c * boostW c = -1 := by
  ext k l
  obtain rfl : k = l := Subsingleton.elim k l
  simp only [boostV, boostU, boostW, Matrix.mul_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.one_apply]
  simp
  nlinarith [hcs]

/-! ## A single block-multiplication identity -/

/-- The first half of the form identity, at the level of blocks:
`B J = fromBlocks B₁₁ (−B₁₂) B₂₁ (−B₂₂)`. -/
lemma boost_mul_pmOneMat (i : Fin n) (c s : ℝ) :
    boostMat_poCenterDefs i c s * pmOneMat =
      Matrix.fromBlocks (boostP_poCenterDefs i c) (- boostU i s) (boostV i s) (- boostW c) := by
  rw [boostMat_poCenterDefs, pmOneMat, Matrix.fromBlocks_multiply]
  simp

/-! ## Main statement -/

theorem boostForm (n : ℕ) (i : Fin n) (c s : ℝ) (hcs : c ^ 2 - s ^ 2 = 1) :
    Matrix.transpose (Work.Mostow.boostMat_poCenterDefs i c s) * LeanEval.Geometry.MostowRigidity.pmOneMat *
        Work.Mostow.boostMat_poCenterDefs i c s = LeanEval.Geometry.MostowRigidity.pmOneMat ∧
    Work.Mostow.boostMat_poCenterDefs i c s * LeanEval.Geometry.MostowRigidity.pmOneMat *
        Matrix.transpose (Work.Mostow.boostMat_poCenterDefs i c s) = LeanEval.Geometry.MostowRigidity.pmOneMat := by
  have hsym : Matrix.transpose (boostMat_poCenterDefs i c s) = boostMat_poCenterDefs i c s := boost_transpose i c s
  have key : boostMat_poCenterDefs i c s * pmOneMat * boostMat_poCenterDefs i c s = pmOneMat := by
    rw [boost_mul_pmOneMat, boostMat_poCenterDefs, Matrix.fromBlocks_multiply, pmOneMat, Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Matrix.neg_mul, ← sub_eq_add_neg,
        boostP_mul_boostP_sub_boostU_mul_boostV i c s hcs]
    · rw [Matrix.neg_mul, ← sub_eq_add_neg,
        boostP_mul_boostU_eq_boostU_mul_boostW i c s, sub_self]
    · rw [Matrix.neg_mul, ← sub_eq_add_neg,
        boostV_mul_boostP_eq_boostW_mul_boostV i c s, sub_self]
    · rw [Matrix.neg_mul, ← sub_eq_add_neg,
        boostV_mul_boostU_sub_boostW_mul_boostW i c s hcs]
  exact ⟨by rw [hsym]; exact key, by rw [hsym]; exact key⟩

end

end Work.Mostow

import Mathlib
import Submission.Work.WilE7.CoreStep.VertIncl

namespace Work.WilE7.CoreStep

theorem submatrixMulVecComp (n m k : ℕ) (A : Matrix (Fin k) (Fin (0 + (n + (m + 1)))) ℝ) :
    (A.submatrix id (fun l : Fin (m + 1) => Fin.natAdd 0 (Fin.natAdd n l))).mulVecLin
      = A.mulVecLin.comp (Work.WilE7.CoreStep.vertIncl n m) := by
  apply LinearMap.ext
  intro x
  funext i
  rw [LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
  -- Both sides are now `Matrix.mulVec _ x i`; expand each as an explicit sum.
  have hleft : Matrix.mulVec
        (A.submatrix id (fun l : Fin (m + 1) => Fin.natAdd 0 (Fin.natAdd n l))) x i
      = ∑ l : Fin (m + 1), A i (Fin.natAdd 0 (Fin.natAdd n l)) * x l := by
    simp only [Matrix.mulVec_apply, Matrix.submatrix_apply, Matrix.row, dotProduct, id_eq]
  have hright : Matrix.mulVec A (vertIncl n m x) i
      = ∑ l : Fin (m + 1), A i (Fin.natAdd 0 (Fin.natAdd n l)) * x l := by
    simp only [Matrix.mulVec_apply, Matrix.row, dotProduct]
    -- Split the sum over `Fin (0 + (n + (m+1)))` into the empty base block and the rest,
    -- then the rest into the `Fin n` block (where `vertIncl` vanishes) and the vertical block.
    rw [Fin.sum_univ_add (a := 0) (b := n + (m + 1))]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add]
    rw [Fin.sum_univ_add (a := n) (b := m + 1)]
    have hbase : (∑ j : Fin n, A i (Fin.natAdd 0 (Fin.castAdd (m + 1) j)) *
        vertIncl n m x (Fin.natAdd 0 (Fin.castAdd (m + 1) j))) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [vertIncl_base n m x j, mul_zero]
    rw [hbase, zero_add]
    apply Finset.sum_congr rfl
    intro l _
    rw [vertIncl_vert]
  rw [hleft, hright]

end Work.WilE7.CoreStep

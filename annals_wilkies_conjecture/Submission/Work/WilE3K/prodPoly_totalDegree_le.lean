import Mathlib
import Submission.Work.WilE3K.Elim

namespace Work.WilE3K

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- The scaling factor `1 + X_c²` of an arctan row has total degree at most `2`. -/
theorem one_add_X_sq_totalDegree_le {σ : Type} [DecidableEq σ] (c : σ) :
    (1 + MvPolynomial.X c ^ 2 : MvPolynomial σ ℝ).totalDegree ≤ 2 := by
  calc (1 + MvPolynomial.X c ^ 2 : MvPolynomial σ ℝ).totalDegree
      ≤ max (1 : MvPolynomial σ ℝ).totalDegree (MvPolynomial.X c ^ 2).totalDegree :=
        MvPolynomial.totalDegree_add _ _
    _ ≤ 2 := by simp [MvPolynomial.totalDegree_X_pow]

/-- `E.prodPoly = ∏_j (1 + t_j²)` is a product of `rt + 1` factors of total degree at most `2`,
so its total degree is at most `2 * (rt + 1)`. -/
theorem prodPoly_totalDegree_le {N rt n re : ℕ} (E : Work.WilE3K.ETData N (rt + 1) n re) :
    (E.prodPoly).totalDegree ≤ 2 * (rt + 1) := by
  rw [ETData.prodPoly]
  calc (∏ j : Fin (rt + 1),
          (1 + MvPolynomial.X (Sum.inl (E.tanCoord j)) ^ 2 : EAPoly (N + 1) re)).totalDegree
      ≤ ∑ j : Fin (rt + 1),
          (1 + MvPolynomial.X (Sum.inl (E.tanCoord j)) ^ 2 : EAPoly (N + 1) re).totalDegree :=
        MvPolynomial.totalDegree_finsetProd Finset.univ _
    _ ≤ ∑ _j : Fin (rt + 1), 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact one_add_X_sq_totalDegree_le _
    _ = 2 * (rt + 1) := by simp [Finset.sum_const, Nat.mul_comm, Fintype.card_fin]

end Work.WilE3K

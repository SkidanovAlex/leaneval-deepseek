import Mathlib
import Submission.Work.WilG0.Defs

namespace Work.WilG0

theorem diagPoly_totalDegree_le (n m : ℕ) (ι : Fin m → Fin n) :
    (diagPoly n m ι).totalDegree ≤ 2 := by
  unfold diagPoly
  refine MvPolynomial.totalDegree_finsetSum_le ?_
  intro j _
  have hsq : (MvPolynomial.X (Fin.natAdd n j) - MvPolynomial.X (Fin.castAdd m (ι j))
        : MvPolynomial (Fin (n + m)) ℝ).totalDegree ≤ 1 := by
    calc (MvPolynomial.X (Fin.natAdd n j) - MvPolynomial.X (Fin.castAdd m (ι j))
            : MvPolynomial (Fin (n + m)) ℝ).totalDegree
        ≤ max (MvPolynomial.X (Fin.natAdd n j) : MvPolynomial (Fin (n + m)) ℝ).totalDegree
              (MvPolynomial.X (Fin.castAdd m (ι j)) : MvPolynomial (Fin (n + m)) ℝ).totalDegree :=
          MvPolynomial.totalDegree_sub _ _
      _ = 1 := by rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X, max_self]
  calc ((MvPolynomial.X (Fin.natAdd n j) - MvPolynomial.X (Fin.castAdd m (ι j))) *
          (MvPolynomial.X (Fin.natAdd n j) - MvPolynomial.X (Fin.castAdd m (ι j)))
          : MvPolynomial (Fin (n + m)) ℝ).totalDegree
      ≤ (MvPolynomial.X (Fin.natAdd n j) - MvPolynomial.X (Fin.castAdd m (ι j))
            : MvPolynomial (Fin (n + m)) ℝ).totalDegree +
        (MvPolynomial.X (Fin.natAdd n j) - MvPolynomial.X (Fin.castAdd m (ι j))
            : MvPolynomial (Fin (n + m)) ℝ).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ ≤ 1 + 1 := add_le_add hsq hsq
    _ = 2 := by norm_num

end Work.WilG0

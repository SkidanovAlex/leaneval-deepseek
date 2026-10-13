import Mathlib
import Submission.Work.WilE3K.Elim

namespace Work.WilE3K

open WilkiesDesign.E

theorem dTanPoly_totalDegree_le {N rt n re : ℕ} (E : Work.WilE3K.ETData N (rt + 1) n re)
    (j : Fin (rt + 1)) (c : Fin (N + 1)) :
    (E.dTanPoly j c).totalDegree ≤ 2 := by
  unfold ETData.dTanPoly
  split_ifs with hk hkk
  · rw [MvPolynomial.totalDegree_one]; norm_num
  · rw [MvPolynomial.totalDegree_zero]; norm_num
  · rw [MvPolynomial.totalDegree_neg]
    have hC : (MvPolynomial.C (E.lam j (E.freeIndex c (not_lt.mp hk))) :
        MvPolynomial (Fin (N + 1) ⊕ Fin re) ℝ).totalDegree = 0 :=
      MvPolynomial.totalDegree_C _
    have hX : (1 + MvPolynomial.X (Sum.inl (E.tanCoord j)) ^ 2 :
        MvPolynomial (Fin (N + 1) ⊕ Fin re) ℝ).totalDegree ≤ 2 := by
      have h1 : (1 : MvPolynomial (Fin (N + 1) ⊕ Fin re) ℝ).totalDegree = 0 :=
        MvPolynomial.totalDegree_one
      have h2 : (MvPolynomial.X (Sum.inl (E.tanCoord j)) ^ 2 :
          MvPolynomial (Fin (N + 1) ⊕ Fin re) ℝ).totalDegree ≤ 2 := by
        have hp := MvPolynomial.totalDegree_pow
          (MvPolynomial.X (Sum.inl (E.tanCoord j)) : MvPolynomial (Fin (N + 1) ⊕ Fin re) ℝ) 2
        rw [MvPolynomial.totalDegree_X] at hp
        omega
      calc (1 + MvPolynomial.X (Sum.inl (E.tanCoord j)) ^ 2 :
            MvPolynomial (Fin (N + 1) ⊕ Fin re) ℝ).totalDegree
          ≤ max (1 : MvPolynomial (Fin (N + 1) ⊕ Fin re) ℝ).totalDegree
              (MvPolynomial.X (Sum.inl (E.tanCoord j)) ^ 2 :
                MvPolynomial (Fin (N + 1) ⊕ Fin re) ℝ).totalDegree :=
            MvPolynomial.totalDegree_add _ _
        _ ≤ 2 := by rw [h1]; exact max_le (by norm_num) h2
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    rw [hC]
    omega

end Work.WilE3K

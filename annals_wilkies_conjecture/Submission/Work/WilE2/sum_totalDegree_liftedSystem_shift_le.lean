import Mathlib
import Submission.Work.WilE2.Lift

set_option autoImplicit false

noncomputable section
open Classical
namespace Work.WilE2

open WilkiesDesign WilkiesDesign.E WilkiesConjecture

/-- Adding a constant polynomial does not increase the total degree beyond `P.totalDegree`:
the constant contributes total degree `0`. -/
theorem totalDegree_add_C_le {σ : Type*} (P : MvPolynomial σ ℝ) (x : ℝ) :
    (P + MvPolynomial.C x).totalDegree ≤ P.totalDegree := by
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le le_rfl ?_)
  rw [MvPolynomial.totalDegree_C]
  exact Nat.zero_le _

/-- Degree bound for the lifted system after a constant shift: the `n` lifted equations keep
the degree of the originals and the Rolle determinant contributes `∑ deg F_i + 1`. -/
theorem sum_totalDegree_liftedSystem_shift_le {n s : ℕ} (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1))
    (c : Fin (n + 1) → ℝ) :
    ∑ i : Fin (n + 1), (S.liftedSystem F i + MvPolynomial.C (-(c i))).totalDegree ≤
      2 * (∑ i : Fin n, (F i).totalDegree) + n + 1 := by
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ j : Fin n,
      (S.liftedSystem F (Fin.castSucc j) + MvPolynomial.C (-(c (Fin.castSucc j)))).totalDegree
        ≤ (F j).totalDegree := by
    intro j
    rw [ESys.liftedSystem_castSucc]
    exact (totalDegree_add_C_le _ _).trans (liftP_totalDegree_le _)
  have hsum : (∑ j : Fin n,
        (S.liftedSystem F (Fin.castSucc j) + MvPolynomial.C (-(c (Fin.castSucc j)))).totalDegree)
      ≤ ∑ j : Fin n, (F j).totalDegree :=
    Finset.sum_le_sum fun j _ => h1 j
  have hlast : (S.liftedSystem F (Fin.last n) + MvPolynomial.C (-(c (Fin.last n)))).totalDegree
      ≤ (∑ i : Fin n, (F i).totalDegree) + 1 := by
    rw [ESys.liftedSystem_last]
    exact (totalDegree_add_C_le _ _).trans (ESys.rolleDet_totalDegree_le S F)
  have h := Nat.add_le_add hsum hlast
  omega

end Work.WilE2

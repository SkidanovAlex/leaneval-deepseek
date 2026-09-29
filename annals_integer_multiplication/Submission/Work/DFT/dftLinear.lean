import Mathlib
import Submission.Work.DFT.dftDefs

open scoped BigOperators

namespace Work.DFT

theorem dftLinear (ts : List ℕ) (sgn : ℤ) (a : ℂ) (u v : Fin ts.prod → ℂ) :
    HvdH.dftMulti ts sgn (a • u + v) = a • HvdH.dftMulti ts sgn u + HvdH.dftMulti ts sgn v := by
  funext j
  simp only [HvdH.dftMulti, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intro i _; ring

end Work.DFT

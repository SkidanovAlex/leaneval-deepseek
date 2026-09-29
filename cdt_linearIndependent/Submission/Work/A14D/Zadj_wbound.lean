import Mathlib
import Submission.Work.A14D.Zadj_defs
import Submission.Work.A14D.Zadj_degree

/-!
# Degree bound for the cleared adjoint numerator

If the cleared numerator `PhiNumZ W` equals `PsiZ c · x³(x−1)` (a polynomial of degree `≤ 9`),
then `W` has degree at most `2`.

Indeed, by `Zadj_degree`, for `W ≠ 0` the top coefficient of `PhiNumZ W` sits at degree
`W.natDegree + 7` and equals `9 · lc W · (W.natDegree − 2)²`, which is non-zero whenever
`W.natDegree ≥ 3`.  Hence a non-zero `W` of degree `≥ 3` would force `deg (PhiNumZ W) ≥ 10`,
contradicting `deg (PsiZ c · x³(x−1)) ≤ 9`.
-/

namespace Work.A14D

open Polynomial

theorem Zadj_wbound (W : Polynomial ℂ) (c : Fin 3 → ℂ)
    (hid : PhiNumZ W = PsiZ c * (X ^ 3 * (X - 1))) : W.natDegree ≤ 2 := by
  by_contra h
  have hg : 2 < W.natDegree := not_le.mp h
  have hW : W ≠ 0 := by
    intro h0
    rw [h0] at hg
    simp at hg
  obtain ⟨hnd, hc⟩ := Zadj_degree W hW
  -- top coefficient of `PhiNumZ W` is non-zero for `W.natDegree ≥ 3`
  have hcoeff : (PhiNumZ W).coeff (W.natDegree + 7) ≠ 0 := by
    rw [hc]
    refine mul_ne_zero (mul_ne_zero (by norm_num) (leadingCoeff_ne_zero.mpr hW)) ?_
    exact pow_ne_zero 2 (sub_ne_zero.mpr (by exact_mod_cast (by omega : W.natDegree ≠ 2)))
  -- the right hand side has degree at most `9`
  have hrd : (PsiZ c * (X ^ 3 * (X - 1)) : Polynomial ℂ).natDegree ≤ 9 := by
    have h1 : (PsiZ c).natDegree ≤ 5 := PsiZ_natDegree_le c
    have h2 : (X ^ 3 * (X - 1) : Polynomial ℂ).natDegree ≤ 4 := by compute_degree
    calc (PsiZ c * (X ^ 3 * (X - 1)) : Polynomial ℂ).natDegree
        ≤ (PsiZ c).natDegree + (X ^ 3 * (X - 1) : Polynomial ℂ).natDegree := natDegree_mul_le
      _ ≤ 9 := by omega
  have hzero : (PsiZ c * (X ^ 3 * (X - 1)) : Polynomial ℂ).coeff (W.natDegree + 7) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hid] at hcoeff
  exact hcoeff hzero

end Work.A14D

import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.Zadj_defs
import Submission.Work.A14D.Zadj_op
import Submission.Work.A14D.Zadj_rhs
import Submission.Work.A14D.Zadj_generic
import Submission.Work.A14D.Zadj_singular
import Submission.Work.A14D.Zadj_degree
import Submission.Work.A14D.Zadj_clearing
import Submission.Work.A14D.Zadj_bounds
import Submission.Work.A14D.Zadj_master
import Submission.Work.A14D.Zadj_divisor
import Submission.Work.A14D.Zadj_wbound
import Submission.Work.A14D.Zadj_solve

/-!
# `Work.A14D.adjointZ_no_solution`

The adjoint (= self-adjoint, `P₁ = P₂'`) Zagier equation

`dRat (dRat (P·β)) − dRat (P'·β) + R·β = Σ_{i<3} c_i·y^{−i}·y'`,  `y = x²/(x−1)`,

with `P = x(1−x)(1−9x)`, `P' = 1−20x+27x²`, `R = 9x−3`, has only the trivial solution
`β = 0`, `c = 0`.  Assembly:

* `Zadj_op`: the hypothesis is `LZf β = RhsZ c` with `LZf = P·β'' + P'·β' + R·β`;
* `Zadj_divisor` (+ `Zadj_bounds`, `Zadj_generic`, `Zadj_singular`): `DZ·β = W` is a polynomial,
  `DZ = x²(x−1)` (the divisor bound; the only singularities `0, 1/9, 1` of `LZf` contribute
  `ordAt ≥ −2, 0, −1`);
* `Zadj_master` (+ `Zadj_clearing`): `PhiNumZ W = PsiZ c·x³(x−1)` (the cleared identity);
* `Zadj_wbound` (+ `Zadj_degree`): `W.natDegree ≤ 2`;
* `Zadj_solve`: the resulting `6×6` linear system has only the trivial solution.
-/

open Polynomial

noncomputable section
namespace Work.A14D

theorem adjointZ_no_solution_aux (β : RatFunc ℂ) (c : Fin 3 → ℂ) (h : LZc β = RhsZ c) :
    β = 0 ∧ c = 0 := by
  have hLf : LZf β = RhsZ c := by rw [← h, Zadj_op]
  obtain ⟨hrhs, hrord⟩ := Zadj_rhs c
  obtain ⟨W, hW⟩ := Zadj_divisor hLf hrord
  have hid : PhiNumZ W = PsiZ c * (X ^ 3 * (X - 1)) := Zadj_master hLf hrhs hW
  have hdeg : W.natDegree ≤ 2 := Zadj_wbound W c hid
  have hn : W = Wlin (fun k : Fin 3 => W.coeff (k : ℕ)) := eq_Wlin_of_natDegree_le_two W hdeg
  have hidW : PhiNumZ (Wlin (fun k : Fin 3 => W.coeff (k : ℕ)))
      = PsiZ c * (X ^ 3 * (X - 1)) := by rw [← hn]; exact hid
  obtain ⟨hn0, hc0⟩ := Zadj_solve (fun k : Fin 3 => W.coeff (k : ℕ)) c hidW
  refine ⟨?_, hc0⟩
  have hW0 : W = 0 := by rw [hn, hn0]; simp [Wlin]
  rw [hW0, map_zero] at hW
  rcases mul_eq_zero.mp hW.symm with h' | h'
  · exact absurd h' (RatFunc.algebraMap_ne_zero DZ_ne_zero)
  · exact h'

theorem adjointZ_no_solution (β : RatFunc ℂ) (c : Fin 3 → ℂ)
    (h : Submission.CDT.dRat (Submission.CDT.dRat
            (algebraMap (Polynomial ℂ) (RatFunc ℂ) (X - 10 * X ^ 2 + 9 * X ^ 3) * β))
        - Submission.CDT.dRat ((algebraMap (Polynomial ℂ) (RatFunc ℂ) (1 - 20 * X + 27 * X ^ 2)) * β)
        + (algebraMap (Polynomial ℂ) (RatFunc ℂ) (-3 + 9 * X)) * β
        = ∑ i : Fin 3, (algebraMap ℂ (RatFunc ℂ) (c i)) * rQc i) : β = 0 ∧ c = 0 :=
  adjointZ_no_solution_aux β c h

end Work.A14D

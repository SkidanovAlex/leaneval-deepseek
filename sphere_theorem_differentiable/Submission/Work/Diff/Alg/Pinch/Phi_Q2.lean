import Mathlib
import Submission.Work.Diff.Alg.Pinch.Qop
import Submission.Work.Diff.Alg.Pinch.Q2Defs
import Submission.Work.Diff.Alg.Pinch.Q2TraceSelf
import Submission.Work.Diff.Alg.Pinch.E1_eq_S1
import Submission.Work.Diff.Alg.Pinch.E2_eq_S2
import Submission.Work.Diff.Alg.Pinch.E3_eq_S2
import Submission.Work.Diff.Alg.Pinch.E4_eq_S1

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Phi (Q2 R) X (bar X) = tr (Tmat R X * Rm R)`

The left-hand side, unfolded with `Q2 R i j k l = ∑ p q (2 R i p k q * R j p l q - 2 R i p l q * R j p k q)`,
is `2 * S1 - 2 * S2` (see `Q2Defs`), and the right-hand side, expanded from the definition of
`Tmat = (adMat X)ᴴ * Rm R * adMat X`, is `E1 - E2 - E3 + E4` (`Q2TraceSelf`).
For an algebraic curvature tensor `R` the four sums are matched by index permutations:
`E1 = S1`, `E4 = S1`, `E2 = S2`, `E3 = S2`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

/-- Unfolding `Q2 R` inside `Phi`: the left-hand side is `2 * S1 - 2 * S2`. -/
theorem phiQ2_expand (n : ℕ) (R : Curv4 n) (X : Fin n × Fin n → ℂ) :
    Phi (Q2 R) X (bar X) = 2 * S1 R X - 2 * S2 R X := by
  simp only [Phi, Q2, S1, S2, bar]
  push_cast
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib, sub_mul]
  simp only [Fintype.sum_prod_type]
  simp only [mul_assoc]

theorem Phi_Q2 (n : ℕ) (R : Submission.Diff.Alg.Curv4 n) (hR : Submission.Diff.Alg.IsAlgCurv R)
    (X : Fin n × Fin n → ℂ) :
    Work.Diff.Alg.Pinch.Phi (Work.Diff.Alg.Pinch.Q2 R) X (Work.Diff.Alg.Pinch.bar X)
      = (Work.Diff.Alg.Pinch.Tmat R X * Work.Diff.Alg.Pinch.Rm R).trace := by
  rw [phiQ2_expand, Q2Aux.Q2Trace, E1_eq_S1 n R hR X, E4_eq_S1 n R hR X,
    E2_eq_S2 n R hR X, E3_eq_S2 n R hR X]
  ring

end Work.Diff.Alg.Pinch

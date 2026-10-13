import Mathlib
import Submission.Work.WilE4.CAD.FiberClosureDefs
import Submission.Work.WilE4.CAD.Bounds

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.WilE4.CAD

open MvPolynomial Polynomial

/-- The desired bound in the form in which it is proved by induction: the statement is *not* only
about the initial state `(Z,H)`, because one step of `projSeq` replaces the family `H` by
`projDataT (k+j+1) H`, so the induction has to run over an arbitrary state `S : ProjState k j`. -/
theorem famDeg_projSeq_le_gen {k : ℕ} : ∀ (j : ℕ) (S : ProjState k j),
    famDeg (projSeq k j S).2 ≤ (PBiter j).eval (famDeg S.2)
  | 0, S => le_of_eq (by simp [projSeq, PBiter])
  | (j+1), S => by
      rw [projSeq_succ]
      refine (famDeg_projSeq_le_gen j (downStep k j S)).trans ?_
      have hstep : famDeg (downStep k j S).2 ≤ projDataTBound.eval (famDeg S.2) :=
        famDeg_projDataT_le_bound S.2
      refine (polynomial_eval_mono (PBiter j) hstep).trans (le_of_eq ?_)
      rw [PBiter]
      exact (Polynomial.eval_comp).symm

/-- `famDeg` of the family at the final level of the iterated projection is bounded by the `j`-fold
iterate of `projDataTBound` in `famDeg H`. -/
theorem famDeg_projSeq_le (k j : ℕ) (Z : SAd (k+(j+1))) (H : List (MvPolynomial (Fin (k+(j+1))) ℝ)) :
    famDeg (projSeq k j (Z,H)).2 ≤ (PBiter j).eval (famDeg H) :=
  famDeg_projSeq_le_gen (k := k) j (Z, H)

end Work.WilE4.CAD

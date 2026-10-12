import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1S.n0FunOp_eq_sum_card
import Submission.Work.BoseFixB1S.n0ProjOpPartitionEigen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

theorem n0FunOp_add_const {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (g : ℝ → ℝ) (c : ℝ) (Ψ : Submission.BoseGases.X N → ℝ) :
    Work.BoseFixB1S.n0FunOp volA A (fun r => g r + c) Ψ
      = fun x => Work.BoseFixB1S.n0FunOp volA A g Ψ x + c * Ψ x := by
  funext x
  -- Regroup both functional calculi over the subsets by cardinality
  -- (`n0FunOp_eq_sum_card`), then use the partition of unity
  -- `Σ_S n0ProjOp S Ψ x = Ψ x` (`n0ProjOp_sum_eq`, valid for every `Ψ`).
  have hL := congrFun (n0FunOp_eq_sum_card volA A (fun r => g r + c) Ψ) x
  have hR := congrFun (n0FunOp_eq_sum_card volA A g Ψ) x
  have hP : (∑ S : Finset (Fin N), n0ProjOp volA A S Ψ x) = Ψ x := by
    have h := congrFun (n0ProjOp_sum_eq volA A Ψ) x
    simpa only [Finset.sum_apply] using h
  rw [hL, hR, ← hP, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun S _ => by ring)

end Work.BoseFixB1S

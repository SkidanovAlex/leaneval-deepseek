import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs2.LocPotential
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs2

/-- Please place this result in namespace `Work.UBBInputs2` (file
`Submission/Work/UBBInputs2/integrable_pairSum_v.lean`). Note the statement is written with fully
qualified `MeasureTheory.` names so that it elaborates without any `open`.

Delegated piece of `Work.UBBInputs2.integrable_qLHSBIntegrand`: the dominating function for the
pair-interaction part is integrable over the configuration space. This is a straightforward
corollary of `Submission.BoseGases.pairInt_sq` (`Submission/PairInt.lean`, which you may import):
rewrite `Φ x ^ 2 * ∑ q ∈ pairSet N, ‖v (x q.1 - x q.2)‖` as
`∑ q ∈ pairSet N, Φ x ^ 2 * ‖v (x q.1 - x q.2)‖` (`Finset.mul_sum`), apply
`pairInt_sq` with `v := fun y => ‖v y‖` (obtained from `hv1` by `MeasureTheory.MemLp.norm`)
to each summand, and sum with `MeasureTheory.integrable_finsetSum`. -/
theorem integrable_pairSum_v {N : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hv1 : MeasureTheory.MemLp v 1
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (hΦs : HasCompactSupport Φ) :
    MeasureTheory.Integrable (fun x : Submission.BoseGases.X N =>
      Φ x ^ 2 * ∑ q ∈ Submission.BoseGases.pairSet N, ‖v (x q.1 - x q.2)‖)
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)) := by
  have hv : MeasureTheory.MemLp (fun y : EuclideanSpace ℝ (Fin 3) => ‖v y‖) 1
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := hv1.norm
  rw [show (fun x : Submission.BoseGases.X N =>
        Φ x ^ 2 * ∑ q ∈ Submission.BoseGases.pairSet N, ‖v (x q.1 - x q.2)‖) =
      (fun x : Submission.BoseGases.X N =>
        ∑ q ∈ Submission.BoseGases.pairSet N, Φ x ^ 2 * ‖v (x q.1 - x q.2)‖) from by
    funext x
    rw [Finset.mul_sum]]
  exact MeasureTheory.integrable_finsetSum _
    (fun q _ => Submission.BoseGases.pairInt_sq hv hΦc hΦs q.1 q.2)

end Work.UBBInputs2

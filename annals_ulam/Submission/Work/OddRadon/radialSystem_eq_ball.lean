import Mathlib
import Submission.Work.OddRadon.RadialDefs
import Submission.Work.OddRadon.radialSystem_determined
import Submission.Work.OddRadon.radialSystem_ball

/-!
# The radial system with the ball's data has the ball as its only positive solution

`RadialSystem n ballPhi ballPsi R r` is the two-power radial system for the odd dimension
`d = 2n+1` with the ball's data `Φ α = 2 cos²α`, `Ψ = 0`.  The ball itself solves it
(`radialSystem_ball`), with `R = r = 1` (`ballR`, `ballr`), and by uniqueness of solutions of
the two-power system on the positive quadrant (`radialSystem_determined`) any *positive*
solution is that one.  Hence on `[0, π/2)` (indeed on `[0, π/2]`, the cleared form of the
system being meaningful there as well) a positive solution equals the ball's data.

## Main result

* `radialSystem_eq_ball` — uniqueness of the positive solution for the ball's data.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace Pointwise Interval Topology

namespace Work.OddRadon

theorem radialSystem_eq_ball (n : ℕ) {R r : ℝ → ℝ} (h : RadialSystem n ballPhi ballPsi R r)
    (hpos : ∀ α ∈ Set.Ico 0 (Real.pi / 2), 0 < R α ∧ 0 < r α) :
    Set.EqOn R ballR (Set.Ico 0 (Real.pi / 2)) ∧
      Set.EqOn r ballr (Set.Ico 0 (Real.pi / 2)) :=
  radialSystem_determined n h (radialSystem_ball n) hpos
    (fun _ _ => ⟨by norm_num [ballR], by norm_num [ballr]⟩)

end Work.OddRadon

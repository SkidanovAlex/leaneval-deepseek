import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SolutionDelivery.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Sup

open Set Metric
open scoped Topology

/-- The `L^∞` norm of the vorticity slice `ω(·,t) = ∇×(u(·,t))` is unchanged if the full-space
supremum `⨆ x, ‖ω(x,t)‖` is replaced by the supremum over a ball that contains the support of
the slice.

The hypotheses are exactly the two boxes under which the supremum is computed in the assembly:
`hbdd` bounds the slice by `M` (so the supremum is honest), and `hsupp` says the slice vanishes
off `B(0,R)`.  Together with `0 ≤ R` (so that `B(0,R)` is non-empty, containing `0`) they give
`⨆ x, ‖ω(x,t)‖ = ⨆ x ∈ B(0,R), ‖ω(x,t)‖`. -/
theorem ciSup_norm_vorticity_eq_ciSup_closedBall {u : Work.SolutionDelivery.R3 → ℝ → Work.SolutionDelivery.R3}
    {R t M : ℝ} (hR : 0 ≤ R)
    (hbdd : ∀ x : Work.SolutionDelivery.R3,
      ‖FiniteTimeSingularity.vorticity (fun y => u y t) x‖ ≤ M)
    (hsupp : ∀ x : Work.SolutionDelivery.R3,
      FiniteTimeSingularity.vorticity (fun y => u y t) x ≠ 0 → x ∈ Metric.closedBall 0 R) :
    Work.LWP.vortLInf u t
      = ⨆ x ∈ Metric.closedBall 0 R,
          ‖FiniteTimeSingularity.vorticity (fun y => u y t) x‖ := by
  unfold Work.LWP.vortLInf
  set ω : Work.SolutionDelivery.R3 → ℝ :=
    fun x => ‖FiniteTimeSingularity.vorticity (fun y => u y t) x‖ with hω
  change (⨆ x, ω x) = ⨆ x ∈ Metric.closedBall 0 R, ω x
  -- the slice is nonnegative and bounded above by `M`
  have hω0 : ∀ x, 0 ≤ ω x := fun x => norm_nonneg _
  have hbddω : BddAbove (Set.range ω) := ⟨M, by rintro _ ⟨x, rfl⟩; exact hbdd x⟩
  have hmem0 : (0 : Work.SolutionDelivery.R3) ∈ Metric.closedBall 0 R := by
    rw [Metric.mem_closedBall, dist_self]; exact hR
  -- the truncated function `x ↦ ⨆ (_ : x ∈ B(0,R)), ω x` is bounded above (by `max M 0`)
  have hbdd2 : BddAbove (Set.range (fun x => ⨆ (_ : x ∈ Metric.closedBall 0 R), ω x)) := by
    refine ⟨max M 0, ?_⟩
    rintro _ ⟨x, rfl⟩
    change (⨆ (_ : x ∈ Metric.closedBall 0 R), ω x) ≤ max M 0
    by_cases hx : x ∈ Metric.closedBall 0 R
    · rw [ciSup_pos hx]
      have : ω x ≤ M := by rw [hω]; exact hbdd x
      exact le_trans this (le_max_left _ _)
    · rw [ciSup_neg hx, Real.sSup_empty]; exact le_max_right _ _
  -- consequently the restricted supremum is nonnegative
  have hRHSnonneg : (0:ℝ) ≤ ⨆ x ∈ Metric.closedBall 0 R, ω x := by
    have hle1 : (⨆ (_ : (0:Work.SolutionDelivery.R3) ∈ Metric.closedBall 0 R), ω 0)
        ≤ ⨆ x ∈ Metric.closedBall 0 R, ω x := le_ciSup hbdd2 0
    have hle2 : ω 0 ≤ (⨆ (_ : (0:Work.SolutionDelivery.R3) ∈ Metric.closedBall 0 R), ω 0) :=
      le_of_eq (ciSup_pos (f := fun _ => ω 0) hmem0).symm
    exact le_trans (hω0 0) (le_trans hle2 hle1)
  refine le_antisymm ?_ ?_
  · -- `⨆ x, ω x ≤ ⨆ x ∈ B(0,R), ω x`: the slice vanishes off the ball
    apply ciSup_le
    intro x
    by_cases hx : x ∈ Metric.closedBall 0 R
    · calc ω x = (⨆ (_ : x ∈ Metric.closedBall 0 R), ω x) :=
            (ciSup_pos (f := fun _ => ω x) hx).symm
          _ = (fun y => ⨆ (_ : y ∈ Metric.closedBall 0 R), ω y) x := rfl
          _ ≤ ⨆ y ∈ Metric.closedBall 0 R, ω y := le_ciSup hbdd2 x
    · have hx0 : ω x = 0 := by
        have hv : FiniteTimeSingularity.vorticity (fun y => u y t) x = 0 := by
          by_contra h
          exact hx (hsupp x h)
        rw [hω]
        simp [hv]
      rw [hx0]; exact hRHSnonneg
  · -- `⨆ x ∈ B(0,R), ω x ≤ ⨆ x, ω x`: forget the constraint `x ∈ B(0,R)`
    apply ciSup_le
    intro x
    change (⨆ (_ : x ∈ Metric.closedBall 0 R), ω x) ≤ ⨆ x, ω x
    by_cases hx : x ∈ Metric.closedBall 0 R
    · rw [ciSup_pos hx]; exact le_ciSup hbddω x
    · rw [ciSup_neg hx, Real.sSup_empty]; exact le_trans (hω0 0) (le_ciSup hbddω 0)

end Work.SolutionDelivery.Sup

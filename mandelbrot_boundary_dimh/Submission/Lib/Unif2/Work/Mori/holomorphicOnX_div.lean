import Mathlib
import Submission.Lib.Unif2.Work.Mori.WindingCircle

namespace Work.Mori

/-- **A quotient of holomorphic functions on a Riemann surface with nowhere-vanishing denominator
is holomorphic.**  Chart-locally the chart representation of `fun x => f x / g x` is the quotient of
the chart representations, which is `AnalyticAt.div` at each point of `U` because `g` does not vanish
there.  The quotient analogue of `Submission.HolomorphicOnX.mul` (the workspace has `.mul`, `.sub`,
`.cexp` but no `.div`/`.inv`); needed for the "log-trick" of `NOTES_gap_analysis.md` §H. -/
theorem holomorphicOnX_div {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {f g : X → ℂ} {U : Set X}
    (hf : Submission.HolomorphicOnX f U) (hg : Submission.HolomorphicOnX g U)
    (hne : ∀ x ∈ U, g x ≠ 0) :
    Submission.HolomorphicOnX (fun x => f x / g x) U := by
  intro x hx
  rw [Submission.HolomorphicOnXAt]
  have hcomp : (fun y : X => f y / g y) ∘ (chartAt ℂ x).symm
      = (f ∘ (chartAt ℂ x).symm) / (g ∘ (chartAt ℂ x).symm) := rfl
  rw [hcomp]
  refine (hf x hx).div (hg x hx) ?_
  simp only [Function.comp_apply]
  rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  exact hne x hx

end Work.Mori

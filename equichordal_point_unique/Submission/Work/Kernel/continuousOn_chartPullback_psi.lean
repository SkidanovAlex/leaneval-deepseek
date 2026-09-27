import Mathlib
import Submission.Work.Kernel.continuous_clampedPullback
import Submission.Work.Kernel.GreenCover

namespace Work.Kernel

/-- **Continuity of a cover weight in its own chart** — item 1 of the pole-index assembly.

`Work.Kernel.pairIntegrable_of_logExpansion` needs `hWc`, i.e.
`Continuous (clampedPullback (E.y i) (E.σ i) (E.ψ i))`, and
`Work.Kernel.continuous_clampedPullback` asks for exactly this continuity on the closed `s i`-ball,
plus `htgt` at `σ i` and the support hypothesis — the latter two being `E.htgt i` (weakened by
`E.hσρ i`) and `E.hψsupp i`.

**Proof (much shorter than the obvious gluing sketch, thanks to review):** every point `w` of the
closed `s i`-ball satisfies `dist w ((chartAt ℂ (E.y i)) (E.y i)) ≤ s i < σ i < ρ i`, hence lies in the
`ρ i`-ball, which is inside the chart target by `E.htgt i`.  So the chart is honest at `w`:
`x := (chartAt ℂ (E.y i)).symm w` is in the source with `(chartAt ℂ (E.y i)) x = w`, and `x ∈ Ω` by
`E.hballΩ i`.  Then `E.hψdiff i i x ⟨hΩ, hsrc⟩` is *literally*
`DifferentiableAt ℝ (fun w : ℂ => E.ψ i ((chartAt ℂ (E.y i)).symm w)) w`, giving `ContinuousAt` and
hence `ContinuousOn`.  There is **no** sphere case and no gluing: the whole closed ball sits strictly
inside the `ρ`-ball.  (`E.hψsupp i`, `E.hspos i` and `[T2Space X]` are not used by this route.) -/
theorem continuousOn_chartPullback_psi {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X}
    (E : Work.Kernel.GreenCover ι Ω K a b) (i : ι) :
    ContinuousOn (fun w : ℂ => E.ψ i ((chartAt ℂ (E.y i)).symm w))
      (Metric.closedBall ((chartAt ℂ (E.y i)) (E.y i)) (E.s i)) := by
  intro w hw
  have hdist : dist w ((chartAt ℂ (E.y i)) (E.y i)) ≤ E.s i := Metric.mem_closedBall.mp hw
  have hlt : dist w ((chartAt ℂ (E.y i)) (E.y i)) < E.ρ i :=
    lt_of_le_of_lt hdist (lt_trans (E.hsσ i) (E.hσρ i))
  have hwtgt : w ∈ (chartAt ℂ (E.y i)).target := E.htgt i (Metric.mem_ball.mpr hlt)
  have hright : (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)).symm w) = w :=
    (chartAt ℂ (E.y i)).right_inv hwtgt
  have hsrc : (chartAt ℂ (E.y i)).symm w ∈ (chartAt ℂ (E.y i)).source :=
    (chartAt ℂ (E.y i)).map_target hwtgt
  have hΩ : (chartAt ℂ (E.y i)).symm w ∈ Ω :=
    E.hballΩ i ⟨hsrc, by
      rw [Set.mem_preimage, hright]; exact Metric.mem_ball.mpr hlt⟩
  have hdiff : DifferentiableAt ℝ (fun w : ℂ => E.ψ i ((chartAt ℂ (E.y i)).symm w)) w := by
    have h := E.hψdiff i i ((chartAt ℂ (E.y i)).symm w) ⟨hΩ, hsrc⟩
    rwa [hright] at h
  exact hdiff.continuousAt.continuousWithinAt

end Work.Kernel

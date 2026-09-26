import Mathlib
import Submission.Work.InnermostDisk.Defs
import Submission.Work.InnermostDisk.not_isEssential_of_section
import Submission.Work.InnermostDisk.exists_section_nhds

namespace Work.InnermostDisk

/-!
# Small balls around points of the torus contain only inessential loops

At every point `X` of the standard torus there is a radius `ε > 0` such that every closed
curve of the torus whose image lies in the Euclidean ball `B(X, ε)` is *inessential* (its
winding vector vanishes).

This is the local triviality of the covering of the torus: `Work.InnermostDisk.exists_section_nhds`
produces a neighbourhood `s ⊆ F` of `X` carrying a continuous section `σ` of the
parametrisation `ψ` together with a radius `ε` such that `F ∩ B(X, ε) ⊆ s`, and
`Work.InnermostDisk.not_isEssential_of_section` turns any curve lying in such a chart into a
curve with a periodic lift to the parameter plane, hence of winding vector `0`.
-/

open LeanEval.KnotTheory.PardonDistortion

theorem exists_ball_not_isEssential (X : LeanEval.KnotTheory.PardonDistortion.R3)
    (hX : X ∈ Work.CoreTopology.standard.carrier) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ γ : Work.CoreTopology.ClosedCurve Work.CoreTopology.standard,
      (∀ t : ℝ, γ.γ t ∈ Metric.ball X ε) →
        ¬ Work.CoreTopology.IsEssential Work.CoreTopology.standard γ := by
  obtain ⟨s, σ, -, -, hσ, ε, hεpos, hε⟩ := exists_section_nhds X hX
  refine ⟨ε, hεpos, fun γ hγ => ?_⟩
  exact not_isEssential_of_section (P := Work.CoreTopology.standard) σ hσ (γ := γ)
    (fun t => hε (γ.γ t) (γ.mem t) (Metric.mem_ball.mp (hγ t)))

end Work.InnermostDisk

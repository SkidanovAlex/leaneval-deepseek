import Mathlib
import Submission.Work.Endgame.Defs
import Submission.Work.Endgame.Basic

namespace Work.Endgame

/-- A compact Hausdorff space `M` whose complement at a point `p` is homeomorphic to the open
unit ball `Bⁿ ⊂ ℝⁿ` is homeomorphic to the unit sphere `𝕊ⁿ ⊂ ℝⁿ⁺¹`.

The open unit ball is homeomorphic to `ℝⁿ` via `Homeomorph.unitBall`
(`Homeomorph.unitBall : E ≃ₜ ball 0 1`), so this reduces to
`Work.Endgame.homeomorphSphereOfComplHomeomorph`. -/
theorem nonempty_homeomorph_sphere_of_ball_homeomorph {n : ℕ} {M : Type*} [TopologicalSpace M]
    [T2Space M] [CompactSpace M] (p : M)
    (h : ({p}ᶜ : Set M) ≃ₜ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  ⟨homeomorphSphereOfComplHomeomorph p
    (h.trans (Homeomorph.unitBall (E := EuclideanSpace ℝ (Fin n))).symm)⟩

end Work.Endgame

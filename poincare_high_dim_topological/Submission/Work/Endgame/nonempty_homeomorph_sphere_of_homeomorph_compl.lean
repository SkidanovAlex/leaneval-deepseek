import Mathlib
import Submission.Work.Endgame.Defs
import Submission.Work.Endgame.Basic

namespace Work.Endgame

/-- A compact Hausdorff space `M` whose complement of a point `p` is homeomorphic to `ℝⁿ`
(with the homeomorphism written in the direction `ℝⁿ ≃ₜ {p}ᶜ`) is homeomorphic to the unit
sphere `𝕊ⁿ ⊂ ℝⁿ⁺¹`.

This is `Work.Endgame.homeomorphSphereOfComplHomeomorph` applied to the inverse of the given
homeomorphism. -/
theorem nonempty_homeomorph_sphere_of_homeomorph_compl {n : ℕ} {M : Type*} [TopologicalSpace M]
    [T2Space M] [CompactSpace M] (p : M) (h : EuclideanSpace ℝ (Fin n) ≃ₜ ({p}ᶜ : Set M)) :
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  ⟨homeomorphSphereOfComplHomeomorph p h.symm⟩

end Work.Endgame

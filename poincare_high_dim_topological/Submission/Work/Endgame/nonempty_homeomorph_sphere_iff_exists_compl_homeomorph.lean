import Mathlib
import Submission.Work.Endgame.Defs
import Submission.Work.Endgame.Basic
import Submission.Work.Endgame.nonempty_homeomorph_sphere_of_nonempty_compl_homeomorph
import Submission.Work.Endgame.exists_compl_homeomorph_euclideanSpace_of_homeomorph_sphere

namespace Work.Endgame

/-- **Characterization.** A compact Hausdorff space is homeomorphic to `𝕊ⁿ` if and only if it
has a point whose complement is homeomorphic to `ℝⁿ`.

The forward direction is `Work.Endgame.exists_compl_homeomorph_euclideanSpace_of_homeomorph_sphere`
and the backward direction is
`Work.Endgame.nonempty_homeomorph_sphere_of_nonempty_compl_homeomorph`. -/
theorem nonempty_homeomorph_sphere_iff_exists_compl_homeomorph {n : ℕ} {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M] :
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ↔
      ∃ p : M, Nonempty (({p}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin n)) := by
  constructor
  · rintro ⟨e⟩
    exact exists_compl_homeomorph_euclideanSpace_of_homeomorph_sphere e
  · rintro ⟨p, h⟩
    exact nonempty_homeomorph_sphere_of_nonempty_compl_homeomorph p h

end Work.Endgame

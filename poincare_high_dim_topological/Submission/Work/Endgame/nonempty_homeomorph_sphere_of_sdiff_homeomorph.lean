import Mathlib
import Submission.Work.Endgame.Defs
import Submission.Work.Endgame.Basic

namespace Work.Endgame

/-- A compact Hausdorff space `M` whose complement of a point `p` is homeomorphic to `ℝⁿ`
(via the presentation `Set.univ \ {p}` of the complement) is homeomorphic to the unit
sphere `𝕊ⁿ ⊂ ℝⁿ⁺¹`.

This is `Work.Endgame.homeomorphSphereOfComplHomeomorph` with the complement rewritten from
`Set.univ \ {p}` to the notationally identical `{p}ᶜ`. -/
theorem nonempty_homeomorph_sphere_of_sdiff_homeomorph {n : ℕ} {M : Type*} [TopologicalSpace M]
    [T2Space M] [CompactSpace M] (p : M)
    (h : ((Set.univ \ {p}) : Set M) ≃ₜ EuclideanSpace ℝ (Fin n)) :
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  ⟨homeomorphSphereOfComplHomeomorph p
    ((Homeomorph.setCongr (by ext x; simp : (Set.univ \ {p} : Set M) = {p}ᶜ)).symm.trans h)⟩

end Work.Endgame

import Mathlib
import Submission.Work.Endgame.Defs
import Submission.Work.Endgame.Basic

/-!
# Endgame (finite-rank model space): a compact Hausdorff space with `V ≅ ℝⁿ` as a puncture is `𝕊ⁿ`

This is the `Nonempty` form of `Work.Endgame.homeomorphSphereOfComplHomeomorphOfFinrank`: if
`M` is compact Hausdorff, `p : M`, `V` is a finite-dimensional real normed space of dimension
`n`, and the complement of `p` is homeomorphic to `V`, then `M` is homeomorphic to the unit
sphere `𝕊ⁿ ⊂ ℝⁿ⁺¹`.
-/

open Metric (sphere)

namespace Work.Endgame

theorem nonempty_homeomorph_sphere_of_compl_homeomorph_finrank {n : ℕ} {M V : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (p : M) (hV : Module.finrank ℝ V = n) (h : ({p}ᶜ : Set M) ≃ₜ V) :
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  ⟨homeomorphSphereOfComplHomeomorphOfFinrank p hV h⟩

end Work.Endgame

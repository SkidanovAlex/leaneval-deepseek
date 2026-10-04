import Mathlib
import Submission.Work.Diff.Alg.Pinch.FeasibleCone

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A feasible direction gives a distance bound

If `F` is convex, `x ∈ F` and `d` is a feasible direction at `x` (i.e. `x + s • d ∈ F` for some
`s > 0`), then for all small `h > 0` the point `x + h • v` is within `h ‖v - d‖` of `F`: indeed
convexity puts `x + h • d ∈ F` for `h ≤ s`, and then
`infDist (x + h • v) F ≤ ‖(x + h • v) - (x + h • d)‖ = h ‖v - d‖`.

This is the elementary half of the supporting-hyperplane argument used for the Böhm–Wilking
pinching-set construction (see `Submission/Work/Diff/Alg/Pinch/`).
-/

namespace Work.Diff.Alg.Pinch

theorem infDist_le_of_mem_feasibleCone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Set E} (hFcv : Convex ℝ F) {x : E} (hx : x ∈ F) (v : E) {d : E}
    (hd : d ∈ Work.Diff.Alg.Pinch.feasibleCone F x) :
    ∃ δ > 0, ∀ h : ℝ, 0 < h → h ≤ δ →
      Metric.infDist (x + h • v) F ≤ h * ‖v - d‖ := by
  obtain ⟨s, hs, hsd⟩ := hd
  refine ⟨s, hs, fun h hh hle => ?_⟩
  have hmem : x + h • d ∈ F := feasibleCone_smul_le_mem hFcv hx hs hh.le hle hsd
  calc Metric.infDist (x + h • v) F ≤ dist (x + h • v) (x + h • d) :=
        Metric.infDist_le_dist_of_mem hmem
    _ = ‖h • (v - d)‖ := by rw [dist_eq_norm]; congr 1; module
    _ = h * ‖v - d‖ := by rw [norm_smul, Real.norm_of_nonneg hh.le]

end Work.Diff.Alg.Pinch

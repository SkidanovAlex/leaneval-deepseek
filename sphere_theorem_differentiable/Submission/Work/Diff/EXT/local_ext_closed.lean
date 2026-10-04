import Mathlib
import Submission.Work.Diff.EXT.local_ext_assembly
import Submission.Work.Diff.EXT.shibounds_of_interfaces
import Submission.Work.Diff.EXT.chartBounds_of_shibounds
import Submission.Work.Diff.EXT.local_ext_of_chart_bounds_v2
import Submission.Work.Diff.EXT.metric_equiv_of_curvBound
import Submission.Work.Diff.EXT.curvNormK_jointSmooth
import Submission.Work.Diff.EXT.evolK_of_flow
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.Diff.GE.scalar_max_principle

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `local_ext_of_bounded_curv`, instantiated with the proved pieces

`Work.Diff.EXT.local_ext_assembly` is the (sorry-free) reduction of the `H`-input of the continuation
theorem to the four inputs `ShiBounds`, `hmet` (metric equivalence), `hconv` (chart bounds from Shi's
bounds) and `hext` (smooth extension from chart bounds).  Here those inputs are instantiated with the
proved theorems of the area:

* `shibounds_of_interfaces hLC hSMP curvNormK_jointSmooth evolK_of_flow` (`ShiBounds`, from the
  evolution inequality `EvolK` and the joint smoothness `NormSmoothK` via the scalar maximum
  principle),
* `metric_equiv_of_curvBound`,
* `chartBounds_of_shibounds`,
* `local_ext_of_chart_bounds_v2` (the proved endgame; the older statement
  `local_ext_of_chart_bounds` is left in place but is no longer used).

The corresponding instantiation cannot live in `local_ext_of_bounded_curv.lean` itself, because
`shibounds_of_interfaces` (and `chartBounds_of_shibounds`, `local_ext_of_chart_bounds_v2`) import
that file — `ShiBounds` and `ChartBounds` are defined there — so quoting them there would be
circular.  The theorem `Work.Diff.EXT.local_ext_of_bounded_curv` of that module is therefore *not*
the vehicle of the continuation theorem: `maximal_regularity` uses
`local_ext_of_bounded_curv_closed` below instead.
-/

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false

/-- The `H`-input of the continuation theorem, from the proved Shi-estimate interfaces. -/
theorem local_ext_of_bounded_curv_closed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (G : ℝ → SMet I M) (T C : ℝ) (hT : 0 < T)
    (hflow : IsRicciFlow G T)
    (hbound : ∀ t ∈ Ico 0 T, CurvBound (G t) C) :
    ∃ δ > 0, ∃ H₁ : ℝ → SMet I M,
      JointSmooth H₁ (Ioo (T - δ) (T + δ)) ∧ ∀ t ∈ Ico (T - δ) T, H₁ t = G t := by
  have hLC : LCSmooth I M := Work.Diff.T.lc_smooth
  have hSMP : ScalarMaxPrinciple I M := Work.Diff.GE.scalar_max_principle hLC
  have hSi : ShiBounds (I := I) (M := M) :=
    shibounds_of_interfaces hLC hSMP (curvNormK_jointSmooth hLC) evolK_of_flow
  exact local_ext_assembly (I := I) (M := M) hSi
    (fun G T C hT hflow hbound hC => metric_equiv_of_curvBound G T C hT hC hflow hbound)
    (fun G T C hT hflow hbound hC hmet =>
      chartBounds_of_shibounds hLC G T C hT hC hflow hbound hmet hSi)
    (fun G T hT hflow hb hnd => local_ext_of_chart_bounds_v2 G T hT hflow hb hnd)
    G T C hT hflow hbound

end Work.Diff.EXT

import Mathlib
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.T.metric_pairing_smooth
import Submission.Work.Diff.EXT.covK_spatialDeriv
import Submission.Commons.Geometry.Manifold.VectorField.mvfderivWithin_apply_mlieBracketWithin
import Submission.Work.Diff.EXT.covK_metric_pairing_family
import Submission.Work.Diff.EXT.covK_mlieBracket_family
import Submission.Work.Diff.EXT.covK_koszul_pairing_family
import Submission.Work.Diff.EXT.covK_section_of_pairing_family

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **The Levi-Civita connection along a jointly smooth family of metrics and of fields.**
If the metric family `G` is jointly smooth on an open set `V ⊆ ℝ × M` (`JointMet G V`) and `X`, `Z`
are families of tangent fields jointly smooth on `V` (`JointField`), then so is
`(t,y) ↦ lcOf (G t) (X t) y (Z t y)`.

PROOF HINT: the static template is `Work.EXT.lcSmooth_noBoundary` (`lc_koszul_pairing` +
`lc_section_of_inner`): first show that for every family `W` of jointly smooth fields the pairing
`(t,y) ↦ (G t).inner y (lcOf (G t) (X t) y (Z t y)) (W t y)` is jointly smooth (Koszul formula:
each term is either a pairing `(G t).inner y` of jointly smooth fields — smooth by
`Work.Diff.T.metric_pairing_smooth` and its family version — or a spatial derivative of such a
pairing, smooth by `covK_spatialDeriv`), then conclude that the section itself is jointly smooth by
the family version of `lc_section_of_inner` (a smooth section in a chart is determined by its
pairings against the coordinate frame, the Gram matrix being invertible). -/
theorem covK_lcOfFamily
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {V : Set (ℝ × M)} (hV : IsOpen V) (hG : JointMet G V)
    {X Z : ℝ → TField (I := I) (M := M)} (hX : JointField X V) (hZ : JointField Z V) :
    JointField (fun t ↦ fun y ↦ lcOf (G t) (X t) y (Z t y)) V := by
  refine covK_section_of_pairing_family (I := I) (M := M) hV hG ?_
  intro W hW
  exact covK_koszul_pairing_family (I := I) (M := M) hV hG hX hZ hW

end Work.Diff.EXT

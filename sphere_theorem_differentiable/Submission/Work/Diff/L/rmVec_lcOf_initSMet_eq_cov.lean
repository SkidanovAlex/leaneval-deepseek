import Mathlib
import Submission.Work.Diff.L.Defs
import Submission.Work.Diff.L.lc_eq_cov
import Submission.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The curvature tensor of the ambient metric equals the curvature of `cov`

`Work.Diff.L.lc_eq_cov` shows that a torsion-free metric-compatible connection `cov` agrees with
the Levi-Civita connection `lcOf (initSMet)` of the ambient metric *on smooth vector fields*.
Here we propagate that equality to the curvature tensors: since `rmVec` is `curv` applied to the
`Classical.epsilon`-chosen smooth extensions (`smoothExt`), and `curv` only ever differentiates a
smooth field once, smoothness of `lcOf (initSMet) Z` (contract `LCSmooth`) and the
`smoothExt`-smoothness of the fields is all that is needed.

The two Koszul-formula equalities

* `lcOf initSMet Z y (Y y) = cov Z y (Y y)`  (for smooth `Z`, `Y`, any `y`) and
* `lcOf initSMet Z y (mlieBracket I X Y y) = cov Z y (mlieBracket I X Y y)`

turn the three terms of `curv (lcOf initSMet) X Y Z x` into the three terms of `curv cov X Y Z x`.
-/

set_option linter.unusedSectionVars false

namespace Work.Diff.L

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

section Helpers

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [T2Space M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

/-- **Equality of the curvature tensors on smooth fields.**  A torsion-free, metric-compatible
connection `cov` has the same curvature as `lcOf (initSMet)` when evaluated on smooth fields, because
`curv` applies the connection only once to a smooth field and the two connections agree there. -/
theorem curv_lcOf_initSMet_eq_curv_cov
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov)
    (hLC : LCSmooth I M)
    {X Y Z : Π x : M, TangentSpace I x} (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (hZ : CMDiff ∞ (T% Z)) (x : M) :
    curv (lcOf (initSMet (I := I) (M := M))) X Y Z x = curv cov X Y Z x := by
  -- the intermediate fields of `cov` are smooth, being `∇_Y Z` of a smooth connection
  have hV1 : CMDiff ∞ (T% (fun y : M => cov Z y (Y y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      cov (inferInstance) hZ hY
  have hV2 : CMDiff ∞ (T% (fun y : M => cov Z y (X y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      cov (inferInstance) hZ hX
  -- the two connections agree on these smooth fields
  have e1 : (fun y : M => lcOf (initSMet (I := I) (M := M)) Z y (Y y))
      = fun y : M => cov Z y (Y y) :=
    funext fun y => lc_eq_cov (I := I) (M := M) cov htor hmet hLC Z hZ y (Y y)
  have e2 : (fun y : M => lcOf (initSMet (I := I) (M := M)) Z y (X y))
      = fun y : M => cov Z y (X y) :=
    funext fun y => lc_eq_cov (I := I) (M := M) cov htor hmet hLC Z hZ y (X y)
  -- unfold `curv` on both sides and rewrite each term
  simp only [curv]
  rw [e1, e2,
    lc_eq_cov (I := I) (M := M) cov htor hmet hLC Z hZ x (mlieBracket I X Y x),
    lc_eq_cov (I := I) (M := M) cov htor hmet hLC (fun y : M => cov Z y (Y y)) hV1 x (X x),
    lc_eq_cov (I := I) (M := M) cov htor hmet hLC (fun y : M => cov Z y (X y)) hV2 x (Y x)]

end Helpers

theorem rmVec_lcOf_initSMet_eq_cov
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov)
    (hLC : LCSmooth I M) :
    ∀ (x : M) (u v w : TangentSpace I x),
      rmVec (lcOf (initSMet (I := I) (M := M))) x u v w = rmVec cov x u v w := by
  intro x u v w
  simp only [rmVec]
  exact curv_lcOf_initSMet_eq_curv_cov (I := I) (M := M) cov htor hmet hLC
    (Work.Diff.GE.Gest.smoothExt_contMDiff x u) (Work.Diff.GE.Gest.smoothExt_contMDiff x v)
    (Work.Diff.GE.Gest.smoothExt_contMDiff x w) x

end Work.Diff.L

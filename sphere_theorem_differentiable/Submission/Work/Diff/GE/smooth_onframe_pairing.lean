import Mathlib
import Submission.Work.Diff.GE.bianchi_kato_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the metric pairing of two smooth tangent fields

The frozen interface `Submission.Diff.SMet I M` (a `Bundle.ContMDiffRiemannianMetric`) is used
*explicitly* through its pairing `g.inner x u v`, while the library lemmas about pairing smooth
sections of the tangent bundle (`ContMDiffAt.inner_bundle`) use the instance inner product
obtained by registering `⟨g.toRiemannianMetric⟩` as a `RiemannianBundle`.

This file records the bridge: for two fields `X`, `Y` whose total-space maps
`y ↦ ⟨y, X y⟩`, `y ↦ ⟨y, Y y⟩` are smooth at `x`, the function `y ↦ g.inner y (X y) (Y y)` is
smooth at `x`.  The point is that with `⟨g.toRiemannianMetric⟩` installed locally, the instance
inner product on `TangentSpace I y` *is definitionally* `g.inner y` (see
`Work.Diff.GE.inner_eq_metric`), so `ContMDiffAt.inner_bundle` applies verbatim.

As documented in `Submission/Geodesic.lean` and `Submission/Variation.lean`, the tangent fibre
`TangentSpace I x` is a type synonym for `E` carrying two propositionally equal norms, so the
library lemma must be invoked in *explicit* form (`(F := …) (E := …) (b := …) (v := …) (w := …)`):
with dot notation the elaborator infers the wrong `NormedAddCommGroup` instance for the fibre and
reports "synthesized type class instance is not definitionally equal to expression inferred by
typing rules".
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

theorem smooth_onframe_pairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (g : Submission.Diff.SMet I M) (x : M) {X Y : Π y : M, TangentSpace I y}
    (hX : ContMDiffAt I (I.prod (modelWithCornersSelf ℝ E)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M => Bundle.TotalSpace.mk' E y (X y)) x)
    (hY : ContMDiffAt I (I.prod (modelWithCornersSelf ℝ E)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M => Bundle.TotalSpace.mk' E y (Y y)) x) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M => g.inner y (X y) (Y y)) x := by
  -- Register the metric as the Riemannian structure of the tangent bundle: this also provides the
  -- `IsContMDiffRiemannianBundle` instance needed by `ContMDiffAt.inner_bundle`.
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  exact ContMDiffAt.inner_bundle (F := E) (E := (fun x : M => TangentSpace I x))
    (b := (id : M → M)) (v := X) (w := Y) hX hY

end Work.Diff.GE

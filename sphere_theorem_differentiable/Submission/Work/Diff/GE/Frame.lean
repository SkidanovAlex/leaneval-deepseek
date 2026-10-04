import Mathlib
import Submission.Diff.Grad
import Submission.CurvatureVec
import Submission.Work.Diff.GE.curvbasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The curvature in orthonormal frames: the bridge to the tensor library

The frozen interfaces (`Submission/Diff/Interfaces.lean`, `Submission/Diff/Grad.lean`) package the
pointwise curvature of a metric `g : SMet I M` through `Classical.epsilon`-chosen extensions and
frames: `smoothExt x u`, `rmVec (lcOf g) x u v w`, the frame components
`rmFrame g x e i j k l = g.inner x (R(eᵢ,eⱼ)e_l) e_k`, and the frame `onFrame g x`.
`Submission/Work/Diff/GE/curvbasic.lean` records the basic specifications and the multilinearity /
antisymmetry / Bianchi identities of `rmVec`.

This file adds

* `inner_eq_metric`: with `⟨g.toRiemannianMetric⟩` installed as the `RiemannianBundle` instance, the
  instance inner product *is* `g.inner` (this is the bridge between the frozen definitions, which use
  `g.inner`, and the library lemmas, which use the instance);
* `rmVec_eq_curvVec`: `rmVec` agrees with the extension-independent tensor
  `Submission.CurvatureVec.curvVec`;
* the `g.inner`-forms of the algebraic identities of `rmP` (antisymmetry, skew-adjointness) that the
  frame-change calculus uses.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [T2Space M]

/-! ## The metric inner product as an instance -/

theorem inner_eq_metric (g : SMet I M) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ∀ (x : M) (u v : TangentSpace I x), inner ℝ u v = g.inner x u v :=
  fun _ _ _ => rfl

/-! ## The frozen curvature `rmVec` and the tensor `curvVec` -/

section Bridge

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The `Classical.epsilon`-defined curvature `rmVec` agrees with the extension-independent tensor
`Submission.CurvatureVec.curvVec`. -/
theorem rmVec_eq_curvVec (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (u v w : TangentSpace I x) :
    rmVec cov x u v w = Submission.CurvatureVec.curvVec cov x u v w := by
  rw [Submission.CurvatureVec.curvVec_eq cov hcov
    (Work.Diff.GE.smoothExt_cmdiff x u) (Work.Diff.GE.smoothExt_cmdiff x v)
    (Work.Diff.GE.smoothExt_cmdiff x w) (Work.Diff.GE.smoothExt_apply x u)
    (Work.Diff.GE.smoothExt_apply x v) (Work.Diff.GE.smoothExt_apply x w)]
  rfl

/-- Skew-adjointness of `rmVec` for a metric-compatible connection, in `g.inner` form:
`g(R(u,v)w, z) = - g(w, R(u,v)z)`. -/
theorem inner_rmVec_skew (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (x : M) (u v w z : TangentSpace I x) :
    inner ℝ (rmVec cov x u v w) z = -inner ℝ w (rmVec cov x u v z) := by
  rw [rmVec_eq_curvVec cov hcov x u v w, rmVec_eq_curvVec cov hcov x u v z]
  exact Submission.CurvatureVec.inner_curvVec_skew cov hcov hmet x u v w z

end Bridge

/-! ## The `g.inner`-form of the algebraic identities of `rmP`

`rmP g x a b c d = g(R(a,b)d, c)` uses the explicit metric `g.inner`, while the library lemmas about
`curvVec` use the instance inner product of `⟨g.toRiemannianMetric⟩`.  Since the contract `LCSmooth`
is stated with exactly that instance, we can phrase the metric-compatibility-dependent identities of
`rmP` with `hLC : LCSmooth I M` (an instance-free proposition) as hypothesis. -/

/-- Skew-adjointness in the last two indices of the frozen curvature form: for the Levi-Civita
connection of `g`, `rmP g x a b c d = - rmP g x a b d c`. -/
theorem rmP_skew (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (a b c d : TangentSpace I x) :
    rmP g x a b c d = -rmP g x a b d c := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨hcov, -, hmet⟩ := hLC g
  obtain ⟨hcov⟩ := hcov
  have h := inner_rmVec_skew (lcOf g) hcov hmet x a b c d
  have hconv : ∀ (z w : TangentSpace I x), Inner.inner ℝ z w = g.inner x z w := fun z w => rfl
  simp only [rmP]
  rw [g.symm x (rmVec (lcOf g) x a b d) c]
  rw [show g.inner x c (rmVec (lcOf g) x a b d) =
        Inner.inner ℝ c (rmVec (lcOf g) x a b d) from (hconv _ _).symm,
      show g.inner x (rmVec (lcOf g) x a b c) d =
        Inner.inner ℝ (rmVec (lcOf g) x a b c) d from (hconv _ _).symm]
  linarith [h]

/-- Antisymmetry in the first two indices of the frozen curvature form:
`rmP g x a b c d = - rmP g x b a c d`. -/
theorem rmP_antisymm (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (a b c d : TangentSpace I x) :
    rmP g x a b c d = -rmP g x b a c d := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨hcov, -, -⟩ := hLC g
  obtain ⟨hcov⟩ := hcov
  have h := rmVec_antisymm (lcOf g) hcov x a b d
  simp only [rmP]
  rw [h]
  simp

end Work.Diff.GE

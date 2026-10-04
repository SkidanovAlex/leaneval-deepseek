import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.grad_smoothAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary chain rules for `Work.Diff.C.rhess_comp`

This module collects the pointwise chain rules used in the proof of
`Work.Diff.C.rhess_comp` (the second-order chain rule for the Hessian `rhess`).

* `Work.Diff.C.mvfderiv_comp_hasDerivAt`: the manifold directional derivative of
  `fun y ↦ c (g y)` is `c' * (directional derivative of g)`;
* `Work.Diff.C.rgrad_comp_hasDerivAt`: the same statement at the level of gradients
  (`rgrad (c ∘ g) = c' • rgrad g`), obtained from the first by testing against all vectors.

Nothing here is a `sorry`.
-/

namespace Work.Diff.C

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **Chain rule for the manifold directional derivative**, for a real function `c` on the
real line.  If `g` is differentiable at `x` and `c` has derivative `c'` at `g x`, then
`d (c ∘ g) x v = c' * d g x v`. -/
lemma mvfderiv_comp_hasDerivAt {g : M → ℝ} {x : M} (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x)
    {c : ℝ → ℝ} {c' : ℝ} (hc : HasDerivAt c c' (g x)) (v : TangentSpace I x) :
    mvfderiv I (fun y : M => c (g y)) x v = c' * mvfderiv I g x v := by
  have h := mvfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := I)
      (f := g) (g := c) x hc.differentiableAt.mdifferentiableAt hg v
  have hscal : (mvfderiv (I := 𝓘(ℝ, ℝ)) c (g x)) ((mfderiv% g x) v)
      = c' * mvfderiv I g x v := by
    have h1 : (mvfderiv (I := 𝓘(ℝ, ℝ)) c (g x)) ((mfderiv% g x) v)
        = (fderiv ℝ c (g x)) ((mfderiv% g x) v) :=
      congrArg (fun L : ℝ →L[ℝ] ℝ => L ((mfderiv% g x) v)) mvfderiv_eq_fderiv
    rw [h1, show (mfderiv% g x) v = mvfderiv I g x v from rfl,
      hc.hasFDerivAt.fderiv,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]
  exact h.trans hscal

/-- **Chain rule for the gradient.**  If `g` is differentiable at `x` and `c` has derivative `c'`
at `g x`, then `∇(c ∘ g)(x) = c' • ∇g(x)`. -/
lemma rgrad_comp_hasDerivAt {g : M → ℝ} {x : M} (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x)
    {c : ℝ → ℝ} {c' : ℝ} (hc : HasDerivAt c c' (g x)) :
    rgrad (I := I) (fun y : M => c (g y)) x = c' • rgrad (I := I) g x := by
  refine ext_inner_left ℝ (fun v => ?_)
  rw [real_inner_comm (x := rgrad (I := I) (fun y : M => c (g y)) x) (y := v),
    inner_rgrad_mvfderiv, mvfderiv_comp_hasDerivAt hg hc v, inner_smul_right,
    real_inner_comm (x := rgrad (I := I) g x) (y := v), inner_rgrad_mvfderiv]

end Work.Diff.C

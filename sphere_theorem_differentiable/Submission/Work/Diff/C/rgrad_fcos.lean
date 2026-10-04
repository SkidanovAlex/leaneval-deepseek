import Mathlib
import Submission.Work.Diff.C.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- The defining property of the gradient, phrased with the *manifold vector derivative* `mvfderiv`
(so that no type synonym `TangentSpace 𝓘(ℝ,ℝ) ·` appears on the right-hand side). -/
lemma inner_rgrad_mvfderiv_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (F : M → ℝ) (x : M) (v : TangentSpace I x) :
    Inner.inner ℝ (rgrad (I := I) (M := M) F x) v = mvfderiv I F x v := by
  rw [inner_rgrad]
  simp only [mvfderiv]
  rfl

/-- `fcos q = cos ∘ rdist q`, so its gradient is `-sin (rdist q x) • ∇(rdist q)` wherever
`rdist q` is differentiable (in particular where it is `C^∞`).  This is the chain rule for
`rgrad` against the scalar function `cos`. -/
theorem rgrad_fcos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    {q x : M}
    (hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z) x) :
    rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x
      = (-Real.sin (rdist (I := I) (M := M) q x))
        • rgrad (I := I) (M := M) (rdist (I := I) (M := M) q) x := by
  have hg : MDifferentiableAt I (𝓘(ℝ, ℝ)) (fun z : M ↦ rdist (I := I) (M := M) q z) x :=
    hsm.mdifferentiableAt (by simp)
  have hcos : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ))
      Real.cos ((fun z : M ↦ rdist (I := I) (M := M) q z) x) :=
    Real.differentiableAt_cos.mdifferentiableAt
  -- the chain rule at the level of the manifold derivative applied to a vector
  have key : ∀ v : TangentSpace I x,
      mvfderiv I (fun y : M => Real.cos ((fun z : M ↦ rdist (I := I) (M := M) q z) y)) x v
        = -Real.sin (rdist (I := I) (M := M) q x)
            * mvfderiv I (fun z : M ↦ rdist (I := I) (M := M) q z) x v := by
    intro v
    have h := mvfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := I)
      (f := fun z : M ↦ rdist (I := I) (M := M) q z) (g := Real.cos) x hcos hg v
    have hscal :
        (mvfderiv (I := 𝓘(ℝ, ℝ)) Real.cos ((fun z : M ↦ rdist (I := I) (M := M) q z) x))
            ((mfderiv I (𝓘(ℝ, ℝ)) (fun z : M ↦ rdist (I := I) (M := M) q z) x) v)
          = -Real.sin (rdist (I := I) (M := M) q x)
              * mvfderiv I (fun z : M ↦ rdist (I := I) (M := M) q z) x v := by
      have h1 :
          (mvfderiv (I := 𝓘(ℝ, ℝ)) Real.cos ((fun z : M ↦ rdist (I := I) (M := M) q z) x))
              ((mfderiv I (𝓘(ℝ, ℝ)) (fun z : M ↦ rdist (I := I) (M := M) q z) x) v)
            = (fderiv ℝ Real.cos ((fun z : M ↦ rdist (I := I) (M := M) q z) x))
                ((mfderiv I (𝓘(ℝ, ℝ)) (fun z : M ↦ rdist (I := I) (M := M) q z) x) v) :=
        congrArg
          (fun L : ℝ →L[ℝ] ℝ =>
            L ((mfderiv I (𝓘(ℝ, ℝ)) (fun z : M ↦ rdist (I := I) (M := M) q z) x) v))
          mvfderiv_eq_fderiv
      rw [h1,
        show (mfderiv I (𝓘(ℝ, ℝ)) (fun z : M ↦ rdist (I := I) (M := M) q z) x) v
            = mvfderiv I (fun z : M ↦ rdist (I := I) (M := M) q z) x v from rfl,
        (Real.hasDerivAt_cos ((fun z : M ↦ rdist (I := I) (M := M) q z) x)).hasFDerivAt.fderiv,
        ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
      ring
    exact h.trans hscal
  have hmain :
      rgrad (I := I) (M := M)
          (fun y : M => Real.cos ((fun z : M ↦ rdist (I := I) (M := M) q z) y)) x
        = (-Real.sin (rdist (I := I) (M := M) q x))
          • rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) x := by
    refine ext_inner_left ℝ (fun v => ?_)
    rw [real_inner_comm
          (x := rgrad (I := I) (M := M)
            (fun y : M => Real.cos ((fun z : M ↦ rdist (I := I) (M := M) q z) y)) x)
          (y := v),
      inner_rgrad_mvfderiv_local
        (fun y : M => Real.cos ((fun z : M ↦ rdist (I := I) (M := M) q z) y)) x v,
      key v, inner_smul_right,
      real_inner_comm
        (x := rgrad (I := I) (M := M) (fun z : M ↦ rdist (I := I) (M := M) q z) x) (y := v),
      inner_rgrad_mvfderiv_local (fun z : M ↦ rdist (I := I) (M := M) q z) x v]
  rw [show fcos (I := I) (M := M) q
      = (fun y : M => Real.cos (rdist (I := I) (M := M) q y)) from rfl]
  exact hmain

end Work.Diff.C

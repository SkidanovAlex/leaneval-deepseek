import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.grad_smoothAt
import Submission.Work.Diff.C.rhess_comp_aux
import Submission.Work.Diff.C.rgrad_comp_eventuallyEq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The second-order chain rule for the Hessian `rhess` (`Work.Diff.C.rhess_comp`)

For a real function `F` on `M` and a real function `c` on the line, the Hessian (`rhess`) of the
composite `c ∘ F` is

`Hess (c ∘ F)(x)(V, W) = c''(F x) · dF(V) · dF(W) + c'(F x) · Hess F(x)(V, W)`,

i.e. the usual one-dimensional second-order chain rule together with the product rule for the
covariant derivative.

The proof is a three-step computation:

1. `∇(c ∘ F) = (c' ∘ F) · ∇F` **near** `x` (`Work.Diff.C.rgrad_comp_eventuallyEq`); the weak
   pointwise `C^∞` hypotheses suffice for this because only first-order regularity of `F` and `c`
   is used at nearby points;
2. the covariant derivative of a *scalar multiple* of a section is the product rule
   (`IsCovariantDerivativeOn.leibniz`), applied to the field `y ↦ deriv c (F y) • ∇F y`, which
   agrees with `∇(c ∘ F)` near `x` (so the two have the same covariant derivative at `x`);
3. `d(deriv c ∘ F)(x)(V) = c''(F x) · dF(x)(V)` (the chain rule again, with
   `iteratedDeriv 2 c = deriv (deriv c)`), and the pairing of the two resulting terms with `W`.

The only imported ingredient is `Work.Diff.C.rgrad_comp_eventuallyEq` (step 1) together with the
pointwise chain rules `Work.Diff.C.rgrad_comp_hasDerivAt` / `Work.Diff.C.mvfderiv_comp_hasDerivAt`.
-/

namespace Work.Diff.C

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric
theorem rhess_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (c : ℝ → ℝ) (F : M → ℝ) (x : M) (V W : TangentSpace I x)
    (hc : ContDiffAt ℝ ∞ c (F x)) (hF : CMDiffAt ∞ F x) :
    Work.Diff.C.rhess cov (fun y : M => c (F y)) x V W
      = iteratedDeriv 2 c (F x) * (mvfderiv I F x V * mvfderiv I F x W)
        + deriv c (F x) * Work.Diff.C.rhess cov F x V W := by
  -- ## Step 1: smoothness of the composite and of the two gradient fields at `x`
  have hG : CMDiffAt ∞ (fun y : M => c (F y)) x := ContMDiffAt.comp x hc.contMDiffAt hF
  have hgradG : ContMDiffAt I I.tangent (∞ : ℕ∞ω)
      (T% (fun y : M => rgrad (I := I) (fun z : M => c (F z)) y)) x := grad_smoothAt hG
  have hgradF : ContMDiffAt I I.tangent (∞ : ℕ∞ω)
      (T% (fun y : M => rgrad (I := I) F y)) x := grad_smoothAt hF
  -- ## Step 2: `∇(c ∘ F) = (deriv c ∘ F) • ∇F` near `x`
  have heq : (fun y : M => rgrad (I := I) (fun z : M => c (F z)) y) =ᶠ[𝓝 x]
      (fun y : M => deriv c (F y) • rgrad (I := I) F y) := rgrad_comp_eventuallyEq hc hF
  -- the two sections of the tangent bundle agree near `x`
  have heqT : (T% (fun y : M => deriv c (F y) • rgrad (I := I) F y)) =ᶠ[𝓝 x]
      (T% (fun y : M => rgrad (I := I) (fun z : M => c (F z)) y)) := by
    filter_upwards [heq] with y hy
    exact congrArg (fun v : TangentSpace I y => (⟨y, v⟩ : TotalSpace E (TangentSpace I))) hy.symm
  have hGmd : MDifferentiableAt I I.tangent
      (T% (fun y : M => rgrad (I := I) (fun z : M => c (F z)) y)) x :=
    hgradG.mdifferentiableAt (by simp)
  -- hence the scalar-multiple field is differentiable at `x` as well
  have hψsect : MDifferentiableAt I I.tangent
      (T% (fun y : M => deriv c (F y) • rgrad (I := I) F y)) x :=
    hGmd.congr_of_eventuallyEq heqT
  -- ## Step 3: the scalar factor `deriv c ∘ F` is differentiable at `x`
  have hFmd : MDifferentiableAt I 𝓘(ℝ, ℝ) F x := hF.mdifferentiableAt (by simp)
  have hderivc : DifferentiableAt ℝ (deriv c) (F x) :=
    ((hc.of_le (m := (3 : ℕ∞ω)) (by simp)).derivWithin (m := 1)
      (by norm_num)).differentiableAt (by norm_num)
  have hψmd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => deriv c (F y)) x :=
    MDifferentiableAt.comp x hderivc.mdifferentiableAt hFmd
  have hσF : MDifferentiableAt I I.tangent (T% (fun y : M => rgrad (I := I) F y)) x :=
    hgradF.mdifferentiableAt (by simp)
  -- ## Step 4: the product rule for the covariant derivative of `(deriv c ∘ F) • ∇F`
  have hleib := (cov.isCovariantDerivativeOn (s := Set.univ)).leibniz
      (σ := fun y : M => rgrad (I := I) F y) (g := fun y : M => deriv c (F y))
      hσF hψmd (Set.mem_univ x)
  -- ## Step 5: `∇(c ∘ F)` and `(deriv c ∘ F) • ∇F` have the same covariant derivative at `x`
  have hcov : cov (fun y : M => rgrad (I := I) (fun z : M => c (F z)) y) x
      = cov (fun y : M => deriv c (F y) • rgrad (I := I) F y) x :=
    (cov.isCovariantDerivativeOn (s := Set.univ)).congr_of_eventuallyEq hGmd hψsect
      Filter.univ_mem heq
  have hleib' : cov (fun y : M => deriv c (F y) • rgrad (I := I) F y) x
      = deriv c (F x) • cov (fun y : M => rgrad (I := I) F y) x
        + (mvfderiv I (fun y : M => deriv c (F y)) x).smulRight (rgrad (I := I) F x) := by
    rw [show ((fun y : M => deriv c (F y)) • (fun y : M => rgrad (I := I) F y))
        = (fun y : M => deriv c (F y) • rgrad (I := I) F y)
        from funext (fun y => rfl)] at hleib
    exact hleib
  -- ## Step 6: the chain rule for `deriv c ∘ F` and `iteratedDeriv 2 c = deriv (deriv c)`
  have hmvdψ : mvfderiv I (fun y : M => deriv c (F y)) x V
      = iteratedDeriv 2 c (F x) * mvfderiv I F x V := by
    have hcd : HasDerivAt (deriv c) (deriv (deriv c) (F x)) (F x) := hderivc.hasDerivAt
    rw [mvfderiv_comp_hasDerivAt (g := F) hFmd hcd V]
    have h2 : iteratedDeriv 2 c (F x) = deriv (deriv c) (F x) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
    rw [h2]
  -- ## Step 7: unfold `rhess` on both sides and evaluate
  rw [rhess, rhess, hcov, hleib']
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, inner_add_left,
    real_inner_smul_left]
  rw [inner_rgrad_mvfderiv (F := F) (x := x) (v := W), hmvdψ]
  ring

end Work.Diff.C

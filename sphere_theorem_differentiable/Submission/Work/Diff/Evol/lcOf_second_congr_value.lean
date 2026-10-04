import Mathlib
import Submission.Work.Diff.Evol.Vocab

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The second covariant derivative is tensorial in the field

If `∇X = 0` at a point `x` (i.e. `lcOf g X x v = 0` for all `v`), then the map
`σ ↦ ∇_{·}(∇X(σ))` at `x` is tensorial at `x`: it depends only on the value of `σ` at `x`.
Indeed, by the Leibniz rule,
`∇(f • ∇X(σ)) = f • ∇(∇X(σ)) + (df) ⊗ (∇X(σ))`, and the correction term vanishes at `x`
because `∇X` vanishes there.

This is the cocycle/well-definedness statement needed to see that `σ ↦ ∇_{σ}∇_{σ}X` is a
genuine tensor at a critical point of `X`; it is used to compare moving-frame computations of
the second derivative of the curvature.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.Evol

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M]

/-- The section `y ↦ ∇X y` of the endomorphism bundle is differentiable at `x`, whenever `X` is
globally smooth and the connection is smooth. -/
theorem mdifferentiableAt_cov_self
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} [ContMDiffCovariantDerivative cov ∞]
    {X : Π y : M, TangentSpace I y} (hX : CMDiff ∞ (T% X)) (x : M) :
    MDifferentiableAt I (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E)))
      (fun y : M => (⟨y, cov X y⟩ : TotalSpace (E →L[ℝ] E)
        (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y))) x := by
  have hX' : ContMDiffOn I (I.prod (modelWithCornersSelf ℝ E)) (∞ + 1) (T% X) univ := by
    change ContMDiffOn I I.tangent (∞ + 1) (T% X) univ
    rw [contMDiffOn_univ]
    simpa using hX
  have h : ContMDiffOn I (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E))) ∞
      (fun x : M => (⟨x, cov X x⟩ : TotalSpace (E →L[ℝ] E)
        (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))) univ := by
    simpa [CovariantDerivative.toFun] using
      (inferInstance : CovariantDerivative.ContMDiffCovariantDerivative cov ∞).contMDiff.contMDiff
        (σ := X) hX'
  exact (h.contMDiffAt Filter.univ_mem).mdifferentiableAt (by simp)

/-- **Tensoriality of the second covariant derivative in its field slot.**  If `∇X` vanishes at
`x`, then two smooth fields `W`, `W'` with the same value at `x` give the same value of
`∇_{W x}(∇_{·}X(W))` at `x`. -/
theorem cov_second_eq_of_eq
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} [ContMDiffCovariantDerivative cov ∞]
    {x : M} {X W W' : Π y : M, TangentSpace I y}
    (hX : CMDiff ∞ (T% X)) (hW : CMDiff ∞ (T% W)) (hW' : CMDiff ∞ (T% W'))
    (hX0 : ∀ v : TangentSpace I x, cov X x v = 0) (hWW' : W x = W' x) :
    cov (fun y : M => cov X y (W y)) x (W x)
      = cov (fun y : M => cov X y (W' y)) x (W' x) := by
  classical
  have hHom : MDifferentiableAt I (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E)))
      (fun y : M => (⟨y, cov X y⟩ : TotalSpace (E →L[ℝ] E)
        (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y))) x :=
    mdifferentiableAt_cov_self hX x
  have hΦt : TensorialAt I E (fun σ : Π y : M, TangentSpace I y =>
      cov (fun y : M => cov X y (σ y)) x) x := by
    refine ⟨?_, ?_⟩
    · intro f σ hf hσ
      have hS : MDiffAt (T% (fun y : M => cov X y (σ y))) x := hHom.clm_bundle_apply hσ
      change cov (fun y : M => cov X y ((f • σ) y)) x
        = f x • cov (fun y : M => cov X y (σ y)) x
      have h₁ : (fun y : M => cov X y ((f • σ) y)) = fun y : M => f y • cov X y (σ y) := by
        funext y; exact map_smul (cov X y) (f y) (σ y)
      have h₂ : (fun y : M => f y • cov X y (σ y)) = f • (fun y : M => cov X y (σ y)) := rfl
      have h₃ := cov.isCovariantDerivativeOn.leibniz (σ := fun y : M => cov X y (σ y)) hS hf
      have hzero : cov X x (σ x) = 0 := hX0 (σ x)
      rw [h₁, h₂, h₃, hzero, ContinuousLinearMap.smulRight_zero, add_zero]
    · intro σ σ' hσ hσ'
      have hS : MDiffAt (T% (fun y : M => cov X y (σ y))) x := hHom.clm_bundle_apply hσ
      have hS' : MDiffAt (T% (fun y : M => cov X y (σ' y))) x := hHom.clm_bundle_apply hσ'
      change cov (fun y : M => cov X y ((σ + σ') y)) x
        = cov (fun y : M => cov X y (σ y)) x + cov (fun y : M => cov X y (σ' y)) x
      have h₁ : (fun y : M => cov X y ((σ + σ') y))
          = (fun y : M => cov X y (σ y)) + (fun y : M => cov X y (σ' y)) := by
        funext y; exact map_add (cov X y) (σ y) (σ' y)
      rw [h₁, cov.isCovariantDerivativeOn.add hS hS']
  have hpt := hΦt.pointwise (hW.contMDiffAt.mdifferentiableAt (by simp))
    (hW'.contMDiffAt.mdifferentiableAt (by simp)) hWW'
  calc cov (fun y : M => cov X y (W y)) x (W x)
    _ = cov (fun y : M => cov X y (W' y)) x (W x) := congrArg (fun L => L (W x)) hpt
    _ = cov (fun y : M => cov X y (W' y)) x (W' x) :=
        congrArg (fun u => cov (fun y : M => cov X y (W' y)) x u) hWW'

theorem lcOf_second_congr_value
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (X : Π y : M, TangentSpace I y) (hX : Work.Diff.Evol.SmoothField I M X)
    (hX0 : ∀ v : TangentSpace I x, Submission.Diff.lcOf g X x v = 0)
    (W W' : Π y : M, TangentSpace I y)
    (hW : Work.Diff.Evol.SmoothField I M W) (hW' : Work.Diff.Evol.SmoothField I M W')
    (hWW' : W x = W' x) :
    Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g X y (W y)) x (W x)
      = Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g X y (W' y)) x (W' x) := by
  haveI : ContMDiffCovariantDerivative (Submission.Diff.lcOf g) ∞ := (hLC g).1.some
  exact cov_second_eq_of_eq (cov := Submission.Diff.lcOf g) hX hW hW' hX0 hWW'

end Work.Diff.Evol

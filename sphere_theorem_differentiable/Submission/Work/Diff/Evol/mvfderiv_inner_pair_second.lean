import Mathlib
import Submission.Work.Diff.Evol.Vocab
import Submission.Work.EXT.contMDiffCovariantDerivative_lcOf
import Submission.Work.EXT.lcSmooth_noBoundary
import Submission.Work.Diff.C.fcos_hess_pt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The second derivative of the metric pairing along a field

`mvfderiv_inner_pair_second`: for a smooth metric `g`, smooth fields `A`, `B`, `W` and a point `x`,

`W·(W·⟪A,B⟫) = ⟪∇_W∇_W A, B⟫ + ⟪∇_W A, ∇_W B⟫ + ⟪∇_W B, ∇_W A⟫ + ⟪A, ∇_W∇_W B⟫`,

which is the product rule for the Levi-Civita connection applied twice.

Proof: metric compatibility (`mvfderiv_inner_eq_of_isMetricCompatible_pt`, from the C area) gives,
pointwise, `W·⟪A,B⟫ = ⟪∇_W A, B⟫ + ⟪A, ∇_W B⟫`.  The two summands are smooth (the `∇_W A` field is
smooth by `Work.EXT.lcOf_apply_contMDiffAt`, and the pairing of two smooth fields is smooth by
`Work.EXT.pairing_contMDiffAt`), so one may differentiate the sum with `mvfderiv_fun_add` and
apply metric compatibility once more to each summand.
-/

namespace Work.Diff.Evol

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

theorem mvfderiv_inner_pair_second
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x : M)
    {A B : Π y : M, TangentSpace I y}
    (hA : Work.Diff.Evol.SmoothField I M A) (hB : Work.Diff.Evol.SmoothField I M B)
    (W : Π y : M, TangentSpace I y) (hW : Work.Diff.Evol.SmoothField I M W) :
    mvfderiv I (fun y : M =>
        mvfderiv I (fun z : M => g.inner z (A z) (B z)) y (W y)) x (W x)
      = g.inner x (Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g A y (W y))
            x (W x)) (B x)
        + g.inner x (Submission.Diff.lcOf g A x (W x)) (Submission.Diff.lcOf g B x (W x))
        + g.inner x (Submission.Diff.lcOf g B x (W x)) (Submission.Diff.lcOf g A x (W x))
        + g.inner x (A x) (Submission.Diff.lcOf g (fun y : M => Submission.Diff.lcOf g B y (W y))
            x (W x)) := by
  -- Put the metric `g` into the instance position; then `g.inner x` is `Inner.inner ℝ`
  -- definitionally, so the metric-compatibility lemmas apply.
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  -- `lcOf g` is compatible with the metric (challenge's form, i.e. for globally smooth fields)
  have hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible (Submission.Diff.lcOf g) :=
    (Work.EXT.lcSmooth_noBoundary (I := I) (M := M) (g := g)).2.2
  have hAsm : CMDiff ∞ (T% A) := hA
  have hBsm : CMDiff ∞ (T% B) := hB
  have hWsm : CMDiff ∞ (T% W) := hW
  -- The two fields `∇_W A`, `∇_W B` are smooth at `x`.
  have hUc : CMDiffAt ∞ (T% (fun y : M => Submission.Diff.lcOf g A y (W y))) x :=
    Work.EXT.lcOf_apply_contMDiffAt (I := I) g hAsm hWsm.contMDiffAt
  have hVc : CMDiffAt ∞ (T% (fun y : M => Submission.Diff.lcOf g B y (W y))) x :=
    Work.EXT.lcOf_apply_contMDiffAt (I := I) g hBsm hWsm.contMDiffAt
  have hUmd : MDiffAt (T% (fun y : M => Submission.Diff.lcOf g A y (W y))) x :=
    hUc.mdifferentiableAt (by simp)
  have hVmd : MDiffAt (T% (fun y : M => Submission.Diff.lcOf g B y (W y))) x :=
    hVc.mdifferentiableAt (by simp)
  have hAmd : MDiffAt (T% A) x := hAsm.contMDiffAt.mdifferentiableAt (by simp)
  have hBmd : MDiffAt (T% B) x := hBsm.contMDiffAt.mdifferentiableAt (by simp)
  -- Pointwise first derivative: the product rule for the pairing.
  have hpt : (fun y : M => mvfderiv I (fun z : M => g.inner z (A z) (B z)) y (W y))
      = fun y : M => g.inner y (Submission.Diff.lcOf g A y (W y)) (B y)
          + g.inner y (A y) (Submission.Diff.lcOf g B y (W y)) := by
    funext y
    exact Work.Diff.C.mvfderiv_inner_eq_of_isMetricCompatible_pt (I := I) (M := M)
      (cov := Submission.Diff.lcOf g) hmet
      (hAsm.contMDiffAt.mdifferentiableAt (by simp))
      (hBsm.contMDiffAt.mdifferentiableAt (by simp)) (W y)
  rw [hpt]
  -- Smoothness of the two summands, so that the derivative splits.
  have hP : MDiffAt (fun y : M =>
      g.inner y (Submission.Diff.lcOf g A y (W y)) (B y)) x :=
    (Work.EXT.pairing_contMDiffAt (I := I) g hUc hBsm.contMDiffAt).mdifferentiableAt (by simp)
  have hQ : MDiffAt (fun y : M =>
      g.inner y (A y) (Submission.Diff.lcOf g B y (W y))) x :=
    (Work.EXT.pairing_contMDiffAt (I := I) g hAsm.contMDiffAt hVc).mdifferentiableAt (by simp)
  rw [mvfderiv_fun_add hP hQ, ContinuousLinearMap.add_apply]
  -- The second application of metric compatibility to each summand.
  have hPval : mvfderiv I (fun y : M =>
        g.inner y (Submission.Diff.lcOf g A y (W y)) (B y)) x (W x)
      = g.inner x (Submission.Diff.lcOf g
            (fun y : M => Submission.Diff.lcOf g A y (W y)) x (W x)) (B x)
        + g.inner x (Submission.Diff.lcOf g A x (W x)) (Submission.Diff.lcOf g B x (W x)) :=
    Work.Diff.C.mvfderiv_inner_eq_of_isMetricCompatible_pt (I := I) (M := M)
      (cov := Submission.Diff.lcOf g) hmet hUmd hBmd (W x)
  have hQval : mvfderiv I (fun y : M =>
        g.inner y (A y) (Submission.Diff.lcOf g B y (W y))) x (W x)
      = g.inner x (Submission.Diff.lcOf g A x (W x)) (Submission.Diff.lcOf g B x (W x))
        + g.inner x (A x) (Submission.Diff.lcOf g
            (fun y : M => Submission.Diff.lcOf g B y (W y)) x (W x)) :=
    Work.Diff.C.mvfderiv_inner_eq_of_isMetricCompatible_pt (I := I) (M := M)
      (cov := Submission.Diff.lcOf g) hmet hAmd hVmd (W x)
  rw [hPval, hQval]
  rw [g.symm x (Submission.Diff.lcOf g A x (W x)) (Submission.Diff.lcOf g B x (W x))]
  ring

end Work.Diff.Evol

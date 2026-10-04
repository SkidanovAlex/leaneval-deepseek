import Mathlib
import Submission.Work.Diff.GE.EvolB.Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE.EvolB

/-- **Differentiability of the rough Laplacian of the curvature on smooth fields.**  For a smooth
metric `g`, a point `x` and smooth fields `A, B, C, D`, the function
`y ↦ lapRmAt g y (A y) (B y) (C y) (D y)` is differentiable (indeed `C^∞`) at `x`.

This is needed in the assembly of the fixed-vector `∇Rm` evolution: the Clairaut step produces
`mvfderiv I (fun y ↦ lapRmAt (G t) y (A y) … + reactionFormAt … ) x v`, which has to be split into
the `lapRmAt` and the `reactionFormAt` parts (`mvfderiv_add` needs differentiability of both).

Route.  `Work.Diff.GE.onFrameONfield` (PROVED) gives a family `E` of globally smooth fields which is
`g`-orthonormal near `x` and satisfies `E i x = Submission.Diff.onFrame g x i`.  By
`Work.Diff.GE.lapRmAt_trace` (PROVED) applied at each `y` near `x`,
`lapRmAt g y (A y) (B y) (C y) (D y) = ∑ m, cov2Rm g y (E m y) (E m y) (A y) (B y) (C y) (D y)`
(the frame-independence of the trace defining `lapRmAt`), and each summand is `C^∞` in `y` by
`Work.Diff.GE.Kato3.cov2Rm_field_smooth` (PROVED, in
`Submission/Work/Diff/GE/kato_cov3RmExt_field.lean`).  A finite sum of `ContMDiffAt` functions is
`ContMDiffAt`, and `ContMDiffAt → MDifferentiableAt`; the transfer from the sum to `lapRmAt g ·` is
a `Filter.EventuallyEq` argument (`Filter.EventuallyEq.mdifferentiableAt_iff`).  The statement
deliberately asks only for `MDifferentiableAt` (so that no smoothness-level notation is needed in
the statement). -/
theorem lapRmAt_fields_diff_B
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (A B C D : Π y : M, TangentSpace I y)
    (hA : Work.Diff.GE.SmoothField M A) (hB : Work.Diff.GE.SmoothField M B)
    (hC : Work.Diff.GE.SmoothField M C) (hD : Work.Diff.GE.SmoothField M D) :
    MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun y : M ↦ Work.Diff.GE.lapRmAt g y (A y) (B y) (C y) (D y)) x := by
  classical
  -- a family of globally smooth fields, `g`-orthonormal near `x`
  obtain ⟨Ef, hEsm, hEON, hEval⟩ := Work.Diff.GE.onFrameONfield hLC g x
  -- each summand of the trace is `C^∞`
  have hsm : ∀ m : Fin (Module.finrank ℝ E), ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞
      (fun y : M => Work.Diff.GE.cov2Rm g y (Ef m y) (Ef m y) (A y) (B y) (C y) (D y)) :=
    fun m => Work.Diff.GE.Kato3.cov2Rm_field_smooth hLC g (hEsm m) (hEsm m) hA hB hC hD
  -- a finite sum of `C^∞` functions is `C^∞`
  have hsum : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞
      (fun y : M => ∑ m, Work.Diff.GE.cov2Rm g y (Ef m y) (Ef m y) (A y) (B y) (C y) (D y)) := by
    simpa using ContMDiff.sum (t := Finset.univ) (fun m _ => hsm m)
  -- the trace is frame independent, so `lapRmAt` agrees with that sum near `x`
  have heq : (fun y : M => Work.Diff.GE.lapRmAt g y (A y) (B y) (C y) (D y)) =ᶠ[𝓝 x]
      (fun y : M =>
        ∑ m, Work.Diff.GE.cov2Rm g y (Ef m y) (Ef m y) (A y) (B y) (C y) (D y)) := by
    filter_upwards [hEON] with y hy
    exact Work.Diff.GE.lapRmAt_trace hLC g y (fun m => Ef m y) hy (A y) (B y) (C y) (D y)
  exact heq.mdifferentiableAt_iff.mpr (hsum.contMDiffAt.mdifferentiableAt (by simp))

end Work.Diff.GE.EvolB

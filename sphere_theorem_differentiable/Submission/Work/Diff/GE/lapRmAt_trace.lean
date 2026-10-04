import Mathlib
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.GE.kato_cov2RmExt_field
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.onFrame_orthogonal_change
import Submission.Work.Diff.GE.kato_cov3RmExt_field
import Submission.Work.Diff.GE.sum_trace_bilinear_orthogonal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **Frame independence of the trace defining `lapRmAt`.**  `lapRmAt g x a b c d` is the trace
`∑ m, ∇²Rm(e_m,e_m,a,b,c,d)` of the second covariant derivative of the curvature over the
`Classical.epsilon`-chosen frame `onFrame g x`; since `∇²Rm` is a `(0,6)`-tensor and the frame is
orthonormal, the value does not depend on the frame, and may be computed in any `g`-orthonormal
frame `e`.

Route: one needs `ℝ`-bilinearity of `cov2Rm g x` in its first two arguments.  The value-dependence
("the `Ext` pattern is the tensor, so it only sees the values of its field arguments") for
`cov2RmExt` is `Work.Diff.GE.kato_cov2RmExt_field`; together with the `ℝ`-linearity of `mvfderiv` in
its vector argument and of `lcOf g V x ·` this gives the bilinearity (here available as
`Work.Diff.GE.cov2Rm_lin_first` / `cov2Rm_lin_snd`).  Then, writing the change of frame
`e m = ∑ p, A p m • e₀ p` with `∑ m, A p m * A q m = if p = q then 1 else 0`
(`Work.Diff.GE.onFrame_orthogonal_change`, `Work.Diff.GE.sum_trace_bilinear_orthogonal`), the two
traces coincide.  This is the rough-Laplacian analogue of
`Work.Diff.GE.dRmNormSq_eq_sum_of_isONFrame`. -/
theorem lapRmAt_trace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : IsONFrame g x e)
    (a b c d : TangentSpace I x) :
    Work.Diff.GE.lapRmAt g x a b c d
      = ∑ m, Work.Diff.GE.cov2Rm g x (e m) (e m) a b c d := by
  classical
  -- the two frames differ by an orthogonal matrix
  obtain ⟨A, hAorth, hAe⟩ :=
    onFrame_orthogonal_change g x (onFrame g x) e (isONFrame_onFrame g x) he
  have hAA : ∀ j k : Fin (Module.finrank ℝ E), ∑ m, A m j * A m k = if j = k then 1 else 0 := by
    intro j k
    have hAtA := (Matrix.mem_orthogonalGroup_iff' (Fin (Module.finrank ℝ E)) ℝ).mp hAorth
    have h := congrFun (congrFun hAtA j) k
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h
  -- the trace is computed by the abstract bilinear-trace lemma
  have htr := sum_trace_bilinear_orthogonal
      (β := fun u v : TangentSpace I x => cov2Rm g x u v a b c d)
      (fun r s u₁ u₂ w => Kato3.cov2Rm_lin_first (I := I) (M := M) hLC g x r s u₁ u₂ w a b c d)
      (fun r s u v₁ v₂ => Kato3.cov2Rm_lin_snd (I := I) (M := M) hLC g x r s u v₁ v₂ a b c d)
      A (onFrame g x) hAA
  rw [show lapRmAt g x a b c d
        = ∑ m, cov2Rm g x (onFrame g x m) (onFrame g x m) a b c d from rfl]
  rw [show (∑ m, cov2Rm g x (e m) (e m) a b c d)
        = ∑ m, cov2Rm g x (∑ j, A m j • onFrame g x j) (∑ k, A m k • onFrame g x k) a b c d from
      Finset.sum_congr rfl (fun m _ => by simp only [hAe m])]
  exact htr.symm

end Work.Diff.GE

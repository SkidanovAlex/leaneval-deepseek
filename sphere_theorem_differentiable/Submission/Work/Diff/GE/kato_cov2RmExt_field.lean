import Mathlib
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.dRmPhi_slotA
import Submission.Work.Diff.GE.covRm_linear_thd
import Submission.Work.Diff.GE.covRm_linear_fth
import Submission.Work.Diff.GE.cov2RmExt_prelim
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.frame_deps
import Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff
import Submission.Commons.Geometry.Manifold.VectorField.exists_frame_decomposition_of_apply_eq_zero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **The field form of `cov2RmExt`, and its smoothness.**  `cov2RmExt g x u V A B C D` is
`mvfderiv (fun y ↦ covRm g y (V y) (A y) (B y) (C y) (D y)) x u` minus the five Leibniz corrections; it
is the covariant derivative `(∇_u ∇Rm)(V,A,B,C,D)` of the `(0,5)`-tensor `∇Rm`, hence depends only on the
*values* `V x, A x, …` of its five field arguments, and `y ↦ cov2RmExt g y (W y) V A B C D` is smooth
whenever `W V A B C D` are smooth.  The invariance follows from the decomposition of a field vanishing at
`x` as `∑ i, f i • Y i` with `f i x = 0`
(`Commons.Geometry.Manifold.VectorField.exists_frame_decomposition_of_apply_eq_zero`; add the import if
needed), the `C^∞`-multilinearity of `rmP` (`rmP_add_*`, `rmP_smul_*`) and the Leibniz rule for
`mvfderiv`.  Smoothness follows from the field form of `covRm` (`kato_covRm_field`; add the import if
needed) with `mvfderiv_apply_contMDiff` and `contMDiff_cov_apply`. -/
theorem kato_cov2RmExt_field
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (V A B C D V' A' B' C' D' : Π y : M, TangentSpace I y)
    (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    (hV' : CMDiff ∞ (T% V')) (hA' : CMDiff ∞ (T% A')) (hB' : CMDiff ∞ (T% B'))
    (hC' : CMDiff ∞ (T% C')) (hD' : CMDiff ∞ (T% D'))
    (hVx : V x = V' x) (hAx : A x = A' x) (hBx : B x = B' x) (hCx : C x = C' x) (hDx : D x = D' x) :
    (∀ u : TangentSpace I x, cov2RmExt g x u V A B C D = cov2RmExt g x u V' A' B' C' D')
      ∧ (∀ (W : Π y : M, TangentSpace I y), CMDiff ∞ (T% W) →
          CMDiff ∞ (fun y : M ↦ cov2RmExt g y (W y) V A B C D)) := by
  obtain ⟨hcov⟩ := (hLC g).1
  refine ⟨?_, ?_⟩
  · intro u
    rw [cov2RmExt_bind_V (g := g) hLC x u hV hV' hA hB hC hD hVx,
      cov2RmExt_bind_A (g := g) hLC x u hV' hA hA' hB hC hD hAx,
      cov2RmExt_bind_B (g := g) hLC x u hV' hA' hB hB' hC hD hBx,
      cov2RmExt_bind_C (g := g) hLC x u hV' hA' hB' hC hC' hD hCx,
      cov2RmExt_bind_D (g := g) hLC x u hV' hA' hB' hC' hD hD' hDx]
  · intro W hW
    have hdirV : CMDiff ∞ (T% (fun y : M => (lcOf g) V y (W y))) :=
      Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
        (lcOf g) hcov hV hW
    have hdirA : CMDiff ∞ (T% (fun y : M => (lcOf g) A y (W y))) :=
      Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
        (lcOf g) hcov hA hW
    have hdirB : CMDiff ∞ (T% (fun y : M => (lcOf g) B y (W y))) :=
      Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
        (lcOf g) hcov hB hW
    have hdirC : CMDiff ∞ (T% (fun y : M => (lcOf g) C y (W y))) :=
      Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
        (lcOf g) hcov hC hW
    have hdirD : CMDiff ∞ (T% (fun y : M => (lcOf g) D y (W y))) :=
      Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
        (lcOf g) hcov hD hW
    have hΦ : CMDiff ∞ (fun z : M => covRm g z (V z) (A z) (B z) (C z) (D z)) :=
      covRm_fields_smooth (g := g) hLC hV hA hB hC hD
    have h1 : CMDiff ∞ (fun y : M =>
        mvfderiv I (fun z : M => covRm g z (V z) (A z) (B z) (C z) (D z)) y (W y)) :=
      Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hΦ hW
    have h2 : CMDiff ∞ (fun y : M =>
        covRm g y ((lcOf g) V y (W y)) (A y) (B y) (C y) (D y)) :=
      covRm_fields_smooth (g := g) hLC hdirV hA hB hC hD
    have h3 : CMDiff ∞ (fun y : M =>
        covRm g y (V y) ((lcOf g) A y (W y)) (B y) (C y) (D y)) :=
      covRm_fields_smooth (g := g) hLC hV hdirA hB hC hD
    have h4 : CMDiff ∞ (fun y : M =>
        covRm g y (V y) (A y) ((lcOf g) B y (W y)) (C y) (D y)) :=
      covRm_fields_smooth (g := g) hLC hV hA hdirB hC hD
    have h5 : CMDiff ∞ (fun y : M =>
        covRm g y (V y) (A y) (B y) ((lcOf g) C y (W y)) (D y)) :=
      covRm_fields_smooth (g := g) hLC hV hA hB hdirC hD
    have h6 : CMDiff ∞ (fun y : M =>
        covRm g y (V y) (A y) (B y) (C y) ((lcOf g) D y (W y))) :=
      covRm_fields_smooth (g := g) hLC hV hA hB hC hdirD
    have hgoal : (fun y : M => cov2RmExt g y (W y) V A B C D)
        = fun y : M =>
            mvfderiv I (fun z : M => covRm g z (V z) (A z) (B z) (C z) (D z)) y (W y)
              - covRm g y ((lcOf g) V y (W y)) (A y) (B y) (C y) (D y)
              - covRm g y (V y) ((lcOf g) A y (W y)) (B y) (C y) (D y)
              - covRm g y (V y) (A y) ((lcOf g) B y (W y)) (C y) (D y)
              - covRm g y (V y) (A y) (B y) ((lcOf g) C y (W y)) (D y)
              - covRm g y (V y) (A y) (B y) (C y) ((lcOf g) D y (W y)) := by
      funext y
      simp only [cov2RmExt]
    rw [hgoal]
    exact ((((h1.sub h2).sub h3).sub h4).sub h5).sub h6

end Work.Diff.GE

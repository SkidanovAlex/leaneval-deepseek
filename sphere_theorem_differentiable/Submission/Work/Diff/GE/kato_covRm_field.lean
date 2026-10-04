import Mathlib
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.cov2RmExt_prelim

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **The field form of `covRm`, and its smoothness.**  The frozen `covRm g x v a b c d` is defined
with the `Classical.epsilon`-chosen extensions `smoothExt x ·`; replacing those by *arbitrary* smooth
vector fields `A B C D` (the direction `v := V x` is a vector and needs no extension) gives the same
value, namely the Leibniz expression defining the covariant derivative `(∇_v Rm)(a,b,c,d)` of the
curvature tensor.  Consequently the function `y ↦ covRm g y (V y) (A y) (B y) (C y) (D y)` is smooth
whenever `V A B C D` are.  Proof route: unfold `covRm`; the `mvfderiv` part depends on the fields only
through their values at `x` (`mvfderiv_congr_of_eventuallyEq`), so it suffices to show that this
expression is `C^∞(M)`-multilinear in each of `A B C D` and vanishes when the field vanishes at `x`;
write a field `D` with `D x = 0` as `∑ i, f i • Y i` with `f i x = 0`
(`Commons.Geometry.Manifold.VectorField.exists_frame_decomposition_of_apply_eq_zero`; add the import if
needed) and use `rmP_add_*`/`rmP_smul_*` (`NablaRm.lean`) and the Leibniz rule for `mvfderiv`.
Smoothness is then `mvfderiv_apply_contMDiff` plus smoothness of `y ↦ rmP g y (A y) (B y) (C y) (D y)`
(from `rmVec_eq_curvVec`, `contMDiff_cov_apply` and smoothness of the metric pairing). -/
theorem kato_covRm_field
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (V A B C D : Π y : M, TangentSpace I y)
    (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) :
    covRm g x (V x) (A x) (B x) (C x) (D x)
      = mvfderiv I (fun y : M ↦ rmP g y (A y) (B y) (C y) (D y)) x (V x)
        - rmP g x (lcOf g A x (V x)) (B x) (C x) (D x)
        - rmP g x (A x) (lcOf g B x (V x)) (C x) (D x)
        - rmP g x (A x) (B x) (lcOf g C x (V x)) (D x)
        - rmP g x (A x) (B x) (C x) (lcOf g D x (V x))
      ∧ CMDiff ∞ (fun y : M ↦ covRm g y (V y) (A y) (B y) (C y) (D y)) := by
  -- `covRm` on the fields `V A B C D` is the operation `dRmPhi`, which is the displayed Leibniz
  -- expression, and `covRm` on smooth fields is smooth (`Work.Diff.GE.covRm_fields_eq_dRmPhi`,
  -- `Work.Diff.GE.covRm_fields_smooth`, in `Submission/Work/Diff/GE/cov2RmExt_prelim.lean`).
  refine ⟨?_, covRm_fields_smooth (g := g) (V := V) (A := A) (B := B) (C := C) (D := D)
    hLC hV hA hB hC hD⟩
  simpa only [dRmPhi] using
    covRm_fields_eq_dRmPhi (g := g) (V := V) (A := A) (B := B) (C := C) (D := D)
      hLC hV hA hB hC hD x

end Work.Diff.GE

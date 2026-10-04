import Mathlib
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.dRmPhi_slotA
import Submission.Work.Diff.GE.covRm_linear_thd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **`dRmPhi` depends on its second field slot only through the value at `x`.**  `dRmPhi g x v A B C D`
is the Leibniz expression for `(∇_v Rm)(A,B,C,D)` on four smooth fields (`Work.Diff.GE.dRmPhi`), equal
to the frozen `covRm` on the `Classical.epsilon`-extensions (`Work.Diff.GE.covRm_eq_dRmPhi`).  The
template is `Work.Diff.GE.dRmPhi_bind_fst` in `Submission/Work/Diff/GE/dRmPhi_slotA.lean` (slot A):
prove `dRmPhi` is `C^∞(M)`-linear in its second field slot (`dRmPhi_linear_snd`, `dRmPhi_add_snd`,
`dRmPhi_smul_snd`, finite sums `dRmPhi_sum_snd`), that it depends only on the germ
(`dRmPhi_germ_snd`), and hence only on the value at `x`, by writing `B x = 0` as `∑ fᵢ • Yᵢ` with
`fᵢ x = 0` (`exists_frame_decomposition_of_apply_eq_zero`) and using `rmP_add_snd`/`rmP_smul_snd`
together with `mvfderiv_mul` on the smooth function `rmP_fields_smooth hLC g hA hB hC hD`.  In the
linearity computation the Leibniz term `mvfderiv I f x v * rmP g x (A x) (B x) (C x) (D x)` cancels
against the corresponding term of the connection correction
`- rmP g x (A x) (lcOf g (f • B) x v) (C x) (D x)`, exactly as in slot A. -/
theorem dRmPhi_bind_snd
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {g : SMet I M} {x : M} {v : TangentSpace I x} (hLC : LCSmooth I M)
    {A B B' C D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hB' : CMDiff ∞ (T% B'))
    (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    (h : B x = B' x) :
    dRmPhi g x v A B C D = dRmPhi g x v A B' C D :=
  dRmPhi_bind_slotB hLC hA hB hB' hC hD h

end Work.Diff.GE

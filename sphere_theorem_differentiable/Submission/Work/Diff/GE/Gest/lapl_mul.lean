import Mathlib
import Submission.Work.Diff.GE.Gest.Base
import Submission.Work.Diff.GE.Gest.hess_mul_field
import Submission.Work.Diff.GE.Gest.sum_lapl_mul_alg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The product rule for the Laplacian `laplAt`

`Δ(uv) = u Δv + v Δu + 2 g(∇u, ∇v)`, where the last term is written in a `g`-orthonormal frame
`onFrame g x` as `∑ i, (∂ᵢu)(∂ᵢv)`.

The pointwise input is `hess_mul_field` (the product rule for the second derivative along a smooth
field, applied to the fields `smoothExt x (onFrame g x i)` chosen by `hessAt`), and the finite-sum
bookkeeping is `sum_lapl_mul_alg`.
-/

namespace Work.Diff.GE.Gest

open scoped Manifold ContDiff Bundle Topology in
open Submission.Diff Submission.Diff.Alg Bundle ContDiff Set VectorField CovariantDerivative Metric in
theorem lapl_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SMet I M) {u v : M → ℝ} (hu : CMDiff ∞ u) (hv : CMDiff ∞ v) (x : M) :
    laplAt g (fun y => u y * v y) x
      = u x * laplAt g v x + v x * laplAt g u x
        + 2 * ∑ i, mvfderiv I u x (onFrame g x i) * mvfderiv I v x (onFrame g x i) := by
  -- The pointwise Hessian product rule, for the smooth extensions used inside `hessAt`.
  have hhess : ∀ w : TangentSpace I x,
      hessAt g (fun y => u y * v y) x w w
        = u x * hessAt g v x w w + v x * hessAt g u x w w
          + 2 * mvfderiv I u x w * mvfderiv I v x w := by
    intro w
    have hW : CMDiff ∞ (T% (smoothExt x w)) := smoothExt_contMDiff x w
    simpa only [hessAt, smoothExt_apply_self] using
      hess_mul_field g u v hu hv (smoothExt x w) hW x
  -- `laplAt` is the sum of the diagonal Hessian entries in the frame `onFrame g x`.
  simp only [laplAt]
  have h2 : (∑ i, hessAt g (fun y => u y * v y) x (onFrame g x i) (onFrame g x i))
      = ∑ i, (u x * hessAt g v x (onFrame g x i) (onFrame g x i)
              + v x * hessAt g u x (onFrame g x i) (onFrame g x i)
              + 2 * (mvfderiv I u x (onFrame g x i) * mvfderiv I v x (onFrame g x i))) :=
    Finset.sum_congr rfl (fun i _ => by rw [hhess (onFrame g x i)]; ring)
  rw [h2, sum_lapl_mul_alg]

end Work.Diff.GE.Gest

import Mathlib
import Submission.Work.Diff.GE.Gest.Base
import Submission.Work.Diff.GE.Gest.lapl_mul
import Submission.Work.Diff.GE.Gest.lapl_sq
import Submission.Work.Diff.GE.Gest.hess_mul_field

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Δ(u³) = 3u² Δu + 6u |∇u|²`

The cube case of the Laplacian calculus for `laplAt`, obtained by writing `u³ = u · u²` and using
the product rule `lapl_mul` together with the square case `lapl_sq`.  The only extra pointwise
input is the Leibniz rule `d(u²) = 2u·du` (`mvfderiv_mul_apply` from `hess_mul_field`).
-/

namespace Work.Diff.GE.Gest

open scoped Manifold ContDiff Bundle Topology in
open Submission.Diff Submission.Diff.Alg Bundle ContDiff Set VectorField CovariantDerivative Metric in
theorem lapl_cube
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SMet I M) {u : M → ℝ} (hu : CMDiff ∞ u) (x : M) :
    laplAt g (fun y => u y ^ 3) x = 3 * u x ^ 2 * laplAt g u x + 6 * u x * gradSq g u x := by
  -- `u ^ 2` is smooth.
  have hu2 : CMDiff ∞ (fun y : M => u y ^ 2) := hu.pow 2
  -- The pointwise Leibniz rule `d(u²) = 2 u · du`.
  have hd2 : ∀ v : TangentSpace I x,
      mvfderiv I (fun y : M => u y ^ 2) x v = 2 * u x * mvfderiv I u x v := by
    intro v
    have hfun : (fun y : M => u y ^ 2) = fun y : M => u y * u y := by funext y; ring
    rw [hfun, mvfderiv_mul_apply u u hu hu x v]
    ring
  -- the product rule for `u · u²`, rewriting `u³ = u · u²`
  have h := lapl_mul g hu hu2 x
  have hfun : (fun y : M => u y ^ 3) = fun y : M => u y * u y ^ 2 := by funext y; ring
  rw [hfun, h, lapl_sq g hu x]
  -- identify the gradient pairing with `2 u |∇u|²`
  have hsum :
      (∑ i, mvfderiv I u x (onFrame g x i)
          * mvfderiv I (fun y : M => u y ^ 2) x (onFrame g x i))
        = 2 * u x * gradSq g u x := by
    have hpt : ∀ i : Fin (Module.finrank ℝ E),
        mvfderiv I u x (onFrame g x i)
            * mvfderiv I (fun y : M => u y ^ 2) x (onFrame g x i)
          = 2 * u x * (mvfderiv I u x (onFrame g x i)) ^ 2 := by
      intro i; rw [hd2 (onFrame g x i)]; ring
    rw [Finset.sum_congr rfl (fun i _ => hpt i), gradSq, Finset.mul_sum]
  rw [hsum]
  ring

end Work.Diff.GE.Gest

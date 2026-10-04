import Mathlib
import Submission.Work.Diff.GE.Gest.Base
import Submission.Work.Diff.GE.Gest.lapl_mul

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Δ(u²) = 2u·Δu + 2|∇u|²`

The squared-function case of the product rule for `laplAt`: apply `lapl_mul` with `u = v` and
identify `∑ᵢ (∂ᵢu)(∂ᵢu)` with `gradSq g u x = ∑ᵢ (∂ᵢu)²`.
-/

namespace Work.Diff.GE.Gest

open scoped Manifold ContDiff Bundle Topology in
open Submission.Diff Submission.Diff.Alg Bundle ContDiff Set VectorField CovariantDerivative Metric in
theorem lapl_sq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SMet I M) {u : M → ℝ} (hu : CMDiff ∞ u) (x : M) :
    laplAt g (fun y => u y ^ 2) x = 2 * u x * laplAt g u x + 2 * gradSq g u x := by
  -- the product rule with both factors equal to `u`
  have h := lapl_mul g hu hu x
  have hfun : (fun y : M => u y ^ 2) = fun y : M => u y * u y := by
    funext y; ring
  rw [hfun, h, gradSq]
  simp only [sq]
  ring

end Work.Diff.GE.Gest

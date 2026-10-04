import Mathlib
import Submission.Commons.Geometry.Manifold.VectorField.mvfderivWithin_apply_mlieBracketWithin

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Geometry.Manifold.VectorField

open scoped _root_.Manifold _root_.ContDiff
open _root_.VectorField
open Set

/-- Second directional derivatives along vector fields commute up to the Lie bracket:
`X(Yf) - Y(Xf) = [X,Y]f` at a point, expressed with `mvfderiv`.
Here `X f := fun x => mvfderiv I f x (X x)`. -/
theorem mvfderiv_second_along_fields
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {f : M → F} {X Y : Π x : M, TangentSpace I x} {x : M}
    (hf : CMDiff ∞ f) (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) :
    mvfderiv I (fun y : M => mvfderiv I f y (Y y)) x (X x) =
      mvfderiv I (fun y : M => mvfderiv I f y (X y)) x (Y x)
        + mvfderiv I f x (VectorField.mlieBracket I X Y x) := by
  have h1 := mvfderivWithin_apply_mlieBracketWithin (s := (univ : Set M)) (x := x)
    uniqueMDiffOn_univ (mem_univ x) (by simp)
    (contMDiffOn_univ.2 hf) (contMDiffOn_univ.2 hX) (contMDiffOn_univ.2 hY)
  simpa [mvfderivWithin_univ, VectorField.mlieBracketWithin_univ] using h1

end Commons.Geometry.Manifold.VectorField

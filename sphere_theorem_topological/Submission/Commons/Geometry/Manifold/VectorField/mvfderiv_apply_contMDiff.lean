import Mathlib.Geometry.Manifold.VectorField.Pullback

namespace Commons.Geometry.Manifold.VectorField

open scoped _root_.Manifold _root_.ContDiff
open _root_.VectorField

/-- The directional derivative `x ↦ d f x (X x)` of a smooth function along a smooth
vector field is again smooth. -/
theorem mvfderiv_apply_contMDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {f : M → F} {X : Π x : M, TangentSpace I x}
    (hf : CMDiff ∞ f) (hX : CMDiff ∞ (T% X)) :
    CMDiff ∞ (fun y : M => mvfderiv I f y (X y)) := by
  -- The bundled derivative of `f` is smooth as a map of tangent bundles.
  have htan : CMDiff ∞ (tangentMap% f) :=
    hf.contMDiff_tangentMap (m := ∞) (n := ∞) le_rfl
  -- Composing with the smooth vector field `X` keeps it smooth.
  have hcomp : CMDiff ∞ (fun y : M => tangentMap% f (T% X y)) :=
    htan.comp hX
  -- The tangent bundle of the model space is trivial, so its second projection is smooth;
  -- this extracts the value of the derivative.
  have hsnd := contMDiff_snd_tangentBundle_modelSpace F (modelWithCornersSelf ℝ F) (n := ∞)
  have hres := hsnd.comp hcomp
  convert hres using 1
  ext y
  simp only [mvfderiv, tangentMap]
  rfl

end Commons.Geometry.Manifold.VectorField
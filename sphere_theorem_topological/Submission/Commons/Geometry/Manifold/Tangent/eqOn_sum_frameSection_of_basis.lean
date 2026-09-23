import Mathlib.Geometry.Manifold.VectorBundle.Tangent

namespace Commons.Geometry.Manifold.Tangent

open scoped _root_.Manifold _root_.ContDiff
open Set

/-- **A section is a sum of coordinate-frame sections.**  On the chart at `x₀`, any section `Z` of
the tangent bundle is the sum of its coordinates in a basis `b` of `E` times the frame sections
`q ↦ T.symmL ℝ q (b i)`. -/
theorem eqOn_sum_frameSection_of_basis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) (x₀ : M)
    (Z : Π x : M, TangentSpace I x) :
    Set.EqOn Z
      (fun y : M => ∑ i, ((b.coord i)
          ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y (Z y)))
        • (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (b i))
      ((chartAt H x₀).source) := by
  intro y hy
  dsimp only
  -- On the chart at `x₀`, `symmL` is a right inverse of `continuousLinearMapAt`.
  have hb : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hy
  have hsym : Z y = (trivializationAt E (TangentSpace I) x₀).symmL ℝ y
      ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y (Z y)) :=
    ((trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt hb (Z y)).symm
  -- The image of `Z y` under `continuousLinearMapAt` is the sum of its `b`-coordinates.
  have hrepr : (∑ i, (b.coord i
        ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y (Z y))) • b i)
      = (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y (Z y) := by
    simpa only [Module.Basis.coord_apply] using
      b.sum_repr ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y (Z y))
  -- `symmL` is linear, so it sends the sum to the sum of the frame sections.
  have key : (∑ i, (b.coord i
        ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y (Z y)))
        • (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (b i))
      = (trivializationAt E (TangentSpace I) x₀).symmL ℝ y
          (∑ i, (b.coord i
            ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y (Z y))) • b i) := by
    rw [map_sum]
    simp_rw [map_smul]
  calc Z y
      = (trivializationAt E (TangentSpace I) x₀).symmL ℝ y
          ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y (Z y)) := hsym
    _ = (trivializationAt E (TangentSpace I) x₀).symmL ℝ y
          (∑ i, (b.coord i
            ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y (Z y))) • b i) := by
        rw [hrepr]
    _ = ∑ i, (b.coord i
          ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y (Z y)))
          • (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (b i) := key.symm

end Commons.Geometry.Manifold.Tangent
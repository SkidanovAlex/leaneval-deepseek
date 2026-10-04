import Submission.Work.Diff.Dim2.Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Pushing a field forward by a linear isometry

The `d = 2` construction identifies the tangent planes `T_pM` and `T_qM` with `ℝ²` by linear
isometries `ep`, `eq` (`Work.Diff.Dim2.exists_isometry_EuclideanTwo`), and then works with the
`ℝ²`-valued fields `uE := ep ∘ u`, `vE2 := eq ∘ vE`.  This file collects the three elementary
transfers: smoothness, the norm, and the differential.
-/

set_option autoImplicit false

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Postcomposition of a field by a linear isometry. -/
def pushField {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (e : F ≃ₗᵢ[ℝ] G) (f : M → F) : M → G := fun x => e (f x)

lemma pushField_apply {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (e : F ≃ₗᵢ[ℝ] G) (f : M → F) (x : M) : pushField e f x = e (f x) := rfl

/-- Smoothness is preserved by pushing forward along a linear isometry. -/
lemma pushField_contMDiffAt {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    {e : F ≃ₗᵢ[ℝ] G} {f : M → F} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, F) ∞ f x) :
    ContMDiffAt I 𝓘(ℝ, G) ∞ (pushField e f) x := by
  have hg : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ (fun z : F => e z) (f x) :=
    (e : F →L[ℝ] G).contMDiffAt
  exact hg.comp x hf

/-- The norm is preserved. -/
lemma pushField_norm {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (e : F ≃ₗᵢ[ℝ] G) (f : M → F) (x : M) : ‖pushField e f x‖ = ‖f x‖ :=
  e.norm_map (f x)

end Work.Diff.Dim2

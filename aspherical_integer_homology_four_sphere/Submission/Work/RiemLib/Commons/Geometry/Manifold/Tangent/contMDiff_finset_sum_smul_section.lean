import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Geometry.Manifold.Tangent

open scoped Manifold ContDiff Topology
open Bundle VectorField Set

/-- **A finite sum of smooth sections of the tangent bundle, with smooth coefficients, is a smooth
section.**  The support condition `tsupport (f i) ⊆ V i` says that the term `f i • W i` is a product
of two smooth objects on the open set `V i` and identically zero on the open set
`(tsupport (f i))ᶜ`; these two open sets cover `M`, so the term, and hence the sum, is smooth on
all of `M`. -/
theorem contMDiff_finset_sum_smul_section {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} (F : Finset ι) (f : ι → M → ℝ) (W : ι → (y : M) → TangentSpace I y)
    (V : ι → Set M) (hV : ∀ i, IsOpen (V i))
    (hf : ∀ i ∈ F, ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ (f i))
    (htsup : ∀ i ∈ F, tsupport (f i) ⊆ V i)
    (hW : ∀ i ∈ F, ContMDiffOn I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, W i y⟩ : Bundle.TotalSpace E (TangentSpace I))) (V i)) :
    ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, ∑ i ∈ F, f i y • W i y⟩ : Bundle.TotalSpace E (TangentSpace I))) := by
  have hterm : ∀ i ∈ F, ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, f i y • W i y⟩ : Bundle.TotalSpace E (TangentSpace I))) := by
    intro i hi
    exact ContMDiffOn.smul_section_of_tsupport (𝕜 := ℝ) (F := E) (V := TangentSpace I)
      (I := I) (n := ∞) (u := V i) ((hf i hi).contMDiffOn) (hV i) (htsup i hi) (hW i hi)
  have hsum := ContMDiff.sum_section (𝕜 := ℝ) (F := E) (V := TangentSpace I) (I := I) (n := ∞)
    (s := F) (t := fun i => f i • W i) (fun i hi => hterm i hi)
  exact hsum

end Commons.Geometry.Manifold.Tangent

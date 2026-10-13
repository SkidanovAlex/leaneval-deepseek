import Mathlib

namespace Work.WilE7.DimAPI

theorem image_mem_nhds_of_hasStrictFDerivAt_bijective {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {x : E} (hf : HasStrictFDerivAt f (fderiv ℝ f x) x)
    (hbij : Function.Bijective (fderiv ℝ f x)) :
    ∀ A ∈ nhds x, f '' A ∈ nhds (f x) := by
  -- Strict differentiability with a surjective derivative gives `map f (𝓝 x) = 𝓝 (f x)`.
  have hrange : (fderiv ℝ f x).range = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact hbij.2
  have hmap : Filter.map f (nhds x) = nhds (f x) := hf.map_nhds_eq_of_surj hrange
  intro A hA
  -- `f '' A` contains the image of any set in `𝓝 x`, in particular `A` itself:
  -- `f ⁻¹' (f '' A) ⊇ A ∈ 𝓝 x`, hence `f '' A ∈ map f (𝓝 x) = 𝓝 (f x)`.
  rw [← hmap]
  exact Filter.mem_map.mpr (Filter.mem_of_superset hA fun y hy => ⟨y, hy, rfl⟩)

end Work.WilE7.DimAPI

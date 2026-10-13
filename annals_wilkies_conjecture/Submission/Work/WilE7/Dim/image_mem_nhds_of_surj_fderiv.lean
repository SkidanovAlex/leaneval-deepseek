import Mathlib

namespace Work.WilE7.Dim

theorem image_mem_nhds_of_surj_fderiv {n m : ℕ} {ψ : (Fin n → ℝ) → (Fin m → ℝ)} {x : Fin n → ℝ}
    (hψ : AnalyticAt ℝ ψ x) (hsurj : Function.Surjective (fderiv ℝ ψ x)) :
    ∀ s ∈ nhds x, ψ '' s ∈ nhds (ψ x) := by
  intro s hs
  -- An analytic map is `C^1`, hence strictly differentiable at `x`.
  have hstrict : HasStrictFDerivAt ψ (fderiv ℝ ψ x) x :=
    (hψ.contDiffAt (n := 1)).hasStrictFDerivAt one_ne_zero
  -- A surjective derivative is a linear map with full range, so the inverse function theorem
  -- applied to the strict derivative gives the open mapping property at `x`.
  have hmap : Filter.map ψ (nhds x) = nhds (ψ x) :=
    hstrict.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hsurj)
  rw [← hmap]
  exact Filter.mem_map.mpr (Filter.mem_of_superset hs (Set.subset_preimage_image ψ s))

end Work.WilE7.Dim

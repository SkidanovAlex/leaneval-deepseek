import Mathlib

namespace Work.WilE3.Lib

/-- If `φ` is strictly differentiable at `z₀` with non-zero derivative `c` and `φ z₀ = 0`, then
for all sufficiently small radii `r` the map `φ` is injective on `Metric.ball z₀ r` and the
image of that ball is a neighbourhood of `0`.

This is proved using the inverse function theorem for `HasStrictDerivAt` (in particular the
local inverse `HasStrictDerivAt.localInverse` and the fact that `φ` maps the neighbourhood
filter of `z₀` onto the neighbourhood filter of `φ z₀ = 0`). -/
theorem exists_ball_injOn_image_mem_nhds {φ : ℂ → ℂ} {z₀ c : ℂ}
    (hφ : HasStrictDerivAt φ c z₀) (hc : c ≠ 0) (hφ0 : φ z₀ = 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      Set.InjOn φ (Metric.ball z₀ r) ∧ φ '' Metric.ball z₀ r ∈ nhds (0 : ℂ) := by
  -- The local inverse is a left inverse of `φ` on a whole ball around `z₀`.
  obtain ⟨R, hRpos, hRsub⟩ := Metric.eventually_nhds_iff.mp (hφ.eventually_left_inverse hc)
  refine ⟨R, hRpos, ?_⟩
  intro r hr hrR
  refine ⟨?_, ?_⟩
  · -- Injectivity on the smaller ball: apply the left inverse to equal images.
    intro z hz w hw hzw
    have hzR : dist z z₀ < R := Metric.ball_subset_ball (le_of_lt hrR) hz
    have hwR : dist w z₀ < R := Metric.ball_subset_ball (le_of_lt hrR) hw
    have h1 := hRsub hzR
    have h2 := hRsub hwR
    rw [hzw] at h1
    exact h1.symm.trans h2
  · -- The image is a neighbourhood of `0` because `φ` maps `𝓝 z₀` to `𝓝 (φ z₀) = 𝓝 0`.
    have hmem : φ '' Metric.ball z₀ r ∈ Filter.map φ (nhds z₀) :=
      Filter.mem_map.mpr (Filter.mem_of_superset (Metric.ball_mem_nhds z₀ hr)
        (Set.subset_preimage_image φ _))
    rwa [hφ.map_nhds_eq hc, hφ0] at hmem

end Work.WilE3.Lib

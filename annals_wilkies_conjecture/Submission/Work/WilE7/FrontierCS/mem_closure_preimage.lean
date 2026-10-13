import Mathlib

open Filter
open scoped Topology

namespace Work.WilE7.FrontierCS

/-- A map with an invertible strict derivative at `p` is a local homeomorphism at `p`, hence
pulls the closure of a set back to the closure of its preimage. -/
theorem mem_closure_preimage {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {Φ : X → Y} {L : X ≃L[ℝ] Y} {p : X} (hΦ : HasStrictFDerivAt Φ (L : X →L[ℝ] Y) p)
    {W : Set Y} (hp : Φ p ∈ closure W) : p ∈ closure (Φ ⁻¹' W) := by
  -- The inverse function theorem: `Φ` maps neighbourhoods of `p` onto neighbourhoods of `Φ p`.
  rw [mem_closure_iff_nhds]
  intro t ht
  have ht' : Φ '' t ∈ 𝓝 (Φ p) := by
    rw [← hΦ.map_nhds_eq_of_equiv]
    exact image_mem_map ht
  obtain ⟨y, hy_mem, hyW⟩ := (mem_closure_iff_nhds.1 hp) (Φ '' t) ht'
  obtain ⟨x, hxt, hxy⟩ := (Set.mem_image Φ t y).1 hy_mem
  exact ⟨x, hxt, by rw [Set.mem_preimage, hxy]; exact hyW⟩

end Work.WilE7.FrontierCS

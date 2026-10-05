import Mathlib

namespace Work.RPB1a.Caratheodory

open Complex Set Metric Filter
open scoped ContDiff Real Topology

/-- The frontier of a set whose frontier is homeomorphic to a circle, with one of its points
removed, is preconnected: a circle with one point removed is a connected open arc. -/
theorem isPreconnected_frontier_diff_singleton {D : Set ℂ}
    (hJ : Nonempty (frontier D ≃ₜ Circle)) {x : ℂ} (hx : x ∈ frontier D) :
    IsPreconnected (frontier D \ {x}) := by
  obtain ⟨e⟩ := hJ
  have hsub : frontier D \ {x}
      = (fun y : Circle => (e.symm y : ℂ)) '' ({e ⟨x, hx⟩}ᶜ : Set Circle) := by
    ext z
    constructor
    · rintro ⟨hz, hzx⟩
      refine ⟨e ⟨z, hz⟩, fun h => hzx (congrArg Subtype.val (e.injective h)), ?_⟩
      show (e.symm (e ⟨z, hz⟩) : ℂ) = z
      simp
    · rintro ⟨y, hy, hyz⟩
      have hyz' : ((e.symm y : frontier D) : ℂ) = z := hyz
      refine ⟨?_, ?_⟩
      · rw [← hyz']; exact (e.symm y).2
      · intro h
        apply hy
        have heq : e.symm y = ⟨x, hx⟩ := Subtype.ext (by rw [hyz', h])
        calc y = e (e.symm y) := (e.apply_symm_apply y).symm
          _ = e ⟨x, hx⟩ := by rw [heq]
  rw [hsub]
  exact (Circle.isPathConnected_compl_singleton (e ⟨x, hx⟩)).isConnected.isPreconnected.image _
    (continuous_subtype_val.comp e.symm.continuous).continuousOn

end Work.RPB1a.Caratheodory

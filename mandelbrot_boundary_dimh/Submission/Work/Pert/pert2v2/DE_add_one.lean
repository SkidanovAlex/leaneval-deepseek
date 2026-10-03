import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic
import Submission.Work.Analysis.PertCrux.basin_fwd_at_phi

namespace Work.Pert.pert2v2

/-- `d.DE = d.Dφ ∩ φ⁻¹(basin)` is closed under `w ↦ w + 1` (the forward half of the `T`-invariance
of the horn-map domain), for a parabolic germ.  `Work.Horn.DE_T_of_phi_maps_to_D0` needs
`φ(Dφ) ⊆ D₀` for this; here only the *basin* membership is used (`basin ⊆ D₀` is free from the
definition of `ParabolicBasin`), and the forward invariance of the basin is the instance
`Work.Analysis.PertCrux.basin_fwd_at_phi` (which needs `hd : IsParabolicGerm f₀ D₀`).

This is the forward sibling of `Work.Pert.DE_down.DE_sub_nat`; it is consumed by the `DR_sub` row of
the two-piece return-map design (shifting the compact `K` into the low chart's window). -/
theorem DE_add_one {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∀ w : ℂ, w ∈ d.DE → w + 1 ∈ d.DE := by
  intro w hw
  obtain ⟨hwφ, hwbasin⟩ := hw
  -- the basin is contained in `D₀` (`n = 0` in the defining `MapsTo`)
  have hD0 : d.φ w ∈ D₀ := by
    obtain ⟨U, hU, hmap, _⟩ := hwbasin
    exact hmap 0 (mem_of_mem_nhds hU)
  -- hence `w + 1` is again in the maximal domain, by `succ_iff`
  have hsucc : w + 1 ∈ d.Dφ := (d.succ_iff w hwφ).mpr hD0
  refine ⟨hsucc, ?_⟩
  -- `φ (w + 1) = f₀ (φ w)`, and the basin is forward invariant along the orbit
  rw [d.φ_abel w hwφ hsucc]
  exact Work.Analysis.PertCrux.basin_fwd_at_phi d hd hwbasin ⟨w, hwφ, rfl⟩
    (d.orbit_avoid (d.φ w) hwbasin)

end Work.Pert.pert2v2

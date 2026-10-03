import Submission.Work.PlanarSC.isPreconnected_sq_preimage_of_contains_circle

namespace Work.PlanarSC

/-- If `Ω` is open and preconnected, misses `0`, and contains a full circle centred at `0`,
then the preimage `{w : ℂ | w ^ 2 ∈ Ω}` of `Ω` under the squaring map is preconnected.

This is immediate from `isPreconnected_sq_preimage_of_contains_circle`: the presence of a circle
centred at `0` inside `Ω` exhibits a point of `Ω` (namely `R`), so the preconnected set `Ω` is
in fact connected. -/
theorem sqrt_preimage_preconnected_of_circle {Ω : Set ℂ} (hΩo : IsOpen Ω)
    (hΩc : IsPreconnected Ω) (h0 : (0 : ℂ) ∉ Ω)
    (hcirc : ∃ R : ℝ, 0 < R ∧ ∀ w : ℂ, ‖w‖ = R → w ∈ Ω) :
    IsPreconnected {w : ℂ | w ^ 2 ∈ Ω} := by
  obtain ⟨R, hRpos, hcircR⟩ := hcirc
  have hmem : (R : ℂ) ∈ Ω := hcircR _ (by simp [abs_of_pos hRpos])
  exact isPreconnected_sq_preimage_of_contains_circle hΩo ⟨⟨(R : ℂ), hmem⟩, hΩc⟩ h0
    ⟨R, hRpos, hcircR⟩

end Work.PlanarSC

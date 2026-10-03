import Mathlib
import Submission.Work.L62.bl_geom_basic

/-!
# `Work.L62.tau0_Bl_ball` — the lower cylinder disc is covered by `τ₀(π(B^ℓ))`

The target of Lemma 6.2's setup: the disc of radius `e^{-2πη}` around the lower-end puncture
`0` of the cylinder is contained in the image `τ₀ (π (B^ℓ))` of the lower component of the
horn map, together with the puncture itself.

The proof is elementary.  A point `ζ ≠ 0` of that disc has `‖ζ‖ < e^{-2πη}`, so its `τ₀`-image
`τ₀ ζ = -1/ζ` has `‖τ₀ ζ‖ = 1/‖ζ‖ > e^{2πη}`; a point of modulus `> e^{2πη}` has a lift in the
lower half plane `{Im < -η} ⊆ B^ℓ` (`Work.L62.mem_piExp_image_Bl_of_norm_gt`, using
`HornData.lower`), and `τ₀` is an involution, so `ζ = τ₀ (π w)` for that lift `w ∈ B^ℓ`.
-/

namespace Work.L62

open MandelDim

theorem tau0_Bl_ball {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) :
    Metric.ball 0 (Real.exp (-(2 * Real.pi * hd.η))) ⊆
      insert 0 (MandelDim.tau0 '' (MandelDim.piExp '' hd.Bl)) := by
  intro ζ hζ
  rcases eq_or_ne ζ 0 with rfl | hne
  · exact Set.mem_insert _ _
  · refine Set.mem_insert_of_mem _ ?_
    -- the disc condition, read as a bound on `‖ζ‖`
    have hζ' : ‖ζ‖ < Real.exp (-(2 * Real.pi * hd.η)) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hζ
    -- `‖τ₀ ζ‖ = 1/‖ζ‖ > e^{2πη}`
    have hnorm : Real.exp (2 * Real.pi * hd.η) < ‖MandelDim.tau0 ζ‖ := by
      have hpos : 0 < ‖ζ‖ := norm_pos_iff.mpr hne
      have h1 : (1 : ℝ) / Real.exp (-(2 * Real.pi * hd.η)) = Real.exp (2 * Real.pi * hd.η) := by
        rw [one_div, ← Real.exp_neg]
        ring_nf
      rw [Work.L62.norm_tau0, ← h1]
      exact one_div_lt_one_div_of_lt hpos hζ'
    have hne' : MandelDim.tau0 ζ ≠ 0 := by
      intro h
      have h2 := Work.L62.tau0_tau0 ζ
      rw [h] at h2
      simp [MandelDim.tau0] at h2
      exact hne h2.symm
    -- hence `τ₀ ζ` has a lift `w` in the lower component
    obtain ⟨w, hw, hwp⟩ := Work.L62.mem_piExp_image_Bl_of_norm_gt d hd hne' hnorm
    -- and `ζ = τ₀ (τ₀ ζ) = τ₀ (π w)`
    exact ⟨MandelDim.piExp w, ⟨w, hw, rfl⟩, by rw [hwp, Work.L62.tau0_tau0]⟩

end Work.L62

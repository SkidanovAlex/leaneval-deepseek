import Mathlib
import Submission.Work.Pert.Ksub2.tau0_phi_band_norm_le

/-!
# `Work.Pert.Ksub2.phi_norm_le_of_far_re_le_one`

The Fatou coordinate `φ = φ₀` of a §4.1-datum is **bounded near `∞` in the whole half-plane
`Re u ≤ 1`**, not only inside Shishikura's repelling sector:

  for every `c > 0` there is `R > 0` with `‖d.φ u‖ ≤ c` for all `u` with `Re u ≤ 1`, `‖u‖ ≥ R`.

The reduction to the sectorial statement `Work.PertCrux.phi_norm_le_of_far` is elementary.  Any
`u` with `Re u ≤ 1` that is *outside* the sector `QLeft ξ₀ = {π/3 < |arg (u + ξ₀)|}` satisfies
`2 Re (u + ξ₀) ≥ ‖u + ξ₀‖` (`Work.Parab.QLeft_iff`, i.e. `|arg| ≤ π/3`), which bounds
`|Im u| ≤ √3 (Re u + ξ₀) ≤ 2 (1 + ξ₀)` and `-ξ₀ ≤ Re u ≤ 1`; hence
`‖u‖ ≤ max ξ₀ 1 + 2 (1 + ξ₀)` (`Work.Pert.Ksub2.norm_le_max_of_not_mem_QLeft`, proved in
`tau0_phi_band_norm_le`).  That bound is *independent of `u`*, so for `‖u‖` beyond it every
admissible `u` lies in the sector, where `φ → 0` by the asymptotic expansion field
`ParabData.φ_asymp`.

(No continuity or compactness argument is needed: the sectorial estimate
`Work.PertCrux.phi_norm_le_of_far` is uniform on `{u ∈ QLeft ξ₀ | ‖u‖ ≥ R₁}`.)
-/

namespace Work.Pert.Ksub2

open MandelDim

/-- **`φ` is uniformly small far out in the half-plane `Re ≤ 1`.**  Since the complement of the
repelling sector inside `{Re ≤ 1}` is bounded by `max ξ₀ 1 + 2 (1 + ξ₀)`, the sectorial estimate
`Work.PertCrux.phi_norm_le_of_far` applies to everything with `‖u‖` beyond that bound. -/
theorem phi_norm_le_of_far_re_le_one {f₀ : ℂ → ℂ} {D₀ : Set ℂ}
    (d : MandelDim.ParabData f₀ D₀) {c : ℝ} (hc : 0 < c) :
    ∃ R : ℝ, 0 < R ∧ ∀ u : ℂ, u.re ≤ 1 → R ≤ ‖u‖ → ‖d.φ u‖ ≤ c := by
  obtain ⟨R₀, hR₀pos, hfar⟩ := Work.PertCrux.phi_norm_le_of_far d hc
  have hξ : 0 < d.ξ₀ := d.ξ₀_pos
  refine ⟨max R₀ (max d.ξ₀ 1 + 2 * (1 + d.ξ₀) + 1), ?_, ?_⟩
  · exact lt_of_lt_of_le hR₀pos (le_max_left _ _)
  · intro u hre hRu
    by_cases hQ : u ∈ MandelDim.QLeft d.ξ₀
    · -- inside the repelling sector: the sectorial estimate applies
      exact hfar u hQ (le_trans (le_max_left _ _) hRu)
    · -- off the sector the point is bounded, hence cannot be that far out
      have hb : ‖u‖ ≤ max d.ξ₀ 1 + 2 * (1 + d.ξ₀) :=
        norm_le_max_of_not_mem_QLeft hre hQ
      have h2 : max d.ξ₀ 1 + 2 * (1 + d.ξ₀) + 1 ≤ ‖u‖ :=
        le_trans (le_max_right _ _) hRu
      linarith

end Work.Pert.Ksub2

import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.LandLeaves.rayAccum_entry
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.ELTop.landsN_iff_landsAt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Classical

noncomputable section

/-! ## The ray point of level `t` lies on the ray, at modulus `t`

The level-`t` point of the dynamic ray `R_c(θ)` (`Work.EL.rayPt hN θ t`) is, by construction,
the inverse image under the Böttcher coordinate of the circle point `t e^{2πiθ}`.  Off the
filled Julia set the dynamical Böttcher coordinate `Work.EL.dynPhi c φ` agrees with `φ`
(`Work.EL.dynPhi_of_notMem`), so these two elementary facts transfer from `Work.Top.NakaneData`
to the `Work.Landing` vocabulary used by `rayAccum`. -/

/-- The Böttcher coordinate of the level-`t` ray point has modulus `t`. -/
theorem norm_phi_rayPt {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {θ t : ℝ} (ht : 1 < t) :
    ‖φ (Work.EL.rayPt hN θ t)‖ = t := by
  have hK : Work.EL.rayPt hN θ t ∉ Work.EL.K c := Work.EL.rayPt_notMem_K hN ht
  rw [← Work.EL.dynPhi_of_notMem (c := c) (φ := φ) hK,
    Work.Top.NakaneData.Phi_rayPt hN ht, Work.Top.NakaneData.norm_rayPoint,
    abs_of_pos (by linarith)]

/-- The level-`t` ray point belongs to the dynamic ray `R_c(θ)`. -/
theorem rayPt_mem_dynRay {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {θ t : ℝ} (ht : 1 < t) :
    Work.EL.rayPt hN θ t ∈ Work.Landing.dynRay c φ θ := by
  have hK : Work.EL.rayPt hN θ t ∉ Work.EL.K c := Work.EL.rayPt_notMem_K hN ht
  refine ⟨(Work.ELTop.escaping_iff_notMem_K c _).mpr hK, ?_⟩
  rw [← Work.EL.dynPhi_of_notMem (c := c) (φ := φ) hK,
    Work.Top.NakaneData.Phi_rayPt hN ht, Work.ELTop.rayPoint_eq_mul_rayDirection]
  exact ⟨t, ht, rfl⟩

/-- **The ray tail at levels near `1` is small.**  If the accumulation set of the dynamic ray
`R_c(θ)` is the singleton `{y}`, then all ray points of level `t` with `1 < t < ρ` are within
`ε` of `y`, for some `ρ > 1` depending on `ε`.

This is the quantitative form of the landing of the ray in the parametrised vocabulary
`Work.EL.rayPt`: it says that the ray point of level `t` tends to the landing point as
`t → 1⁺`, which is `Work.EL.LandsN hN θ y`.

Proof: `Work.LandLeaves.rayAccum_entry` produces a level `ρ > 1` such that *every* point of the
ray of Böttcher modulus `≤ ρ` is within `ε` of `y`; the ray point of level `t < ρ` is such a
point, by `rayPt_mem_dynRay` and `norm_phi_rayPt`. -/
theorem rayPt_tail_small {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) {y : ℂ} {θ : ℝ}
    (h : Work.Landing.rayAccum c φ θ = {y}) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 1 < ρ ∧ ∀ t : ℝ, 1 < t → t < ρ → ‖Work.EL.rayPt hN θ t - y‖ ≤ ε := by
  obtain ⟨ρ, hρ, hρ'⟩ := rayAccum_entry hφ h hε
  exact ⟨ρ, hρ, fun t ht htρ =>
    hρ' _ (rayPt_mem_dynRay hN ht) (by rw [norm_phi_rayPt hN ht]; linarith)⟩

end

end Work.LandLeaves

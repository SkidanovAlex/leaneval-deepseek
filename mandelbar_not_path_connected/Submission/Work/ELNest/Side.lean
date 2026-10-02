/-
# EL nest, part 2 (N0): side preservation at `z₁`

Contract §6 R-a1 (`sidePreserve`).  The two sides of the `α`-pair `Γ₁ = R(α₁) ∪ {z₁} ∪ R(α₂)` are
exchanged with the two petals of the Leau--Fatou flower: the band side (where the nest `Q̂` lives)
is the repelling petal `Ψ(H_R)`, and the attracting petal `Pa` is on the wake side.  Hence `F c`
-- which acts on the flower as `Ψ w ↦ Ψ (w + 1)` -- preserves the side of `Γ₁` near `z₁`, which is
what makes the inverse branch `g` of `F c` agree with the local inverse of `F c` at `z₁`
(`Nest.lean`, `Qnest_shrinks`).

The geometric inputs are the fields `NestData.SP` (the side preservation of the *shift* in the
far-left half-plane, `Work.ELRig.sidePreserve_core`) and `NestData.Pa_far` (HS §2, the petals at a
parabolic point).  Everything else is the flower's `cover` and its functional equation `Ψ_shift`.
This replaces the proof through the (false) field `band`; see `NOTES_LEAD_mandelbar_residuals.md`
§3.3.
-/
import Mathlib
import Submission.Work.ELNest.Setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Topology Function
open scoped Topology ComplexConjugate

noncomputable section

namespace Work.ELNest

open Work.EL

variable {c : ℂ}

/-- **N0** (contract §6 R-a1, `sidePreserve`): near the parabolic point `z₁`, the map
`F c = f_c^{10}` preserves the side of the `α`-pair `Γ₁ = R(α₁) ∪ {z₁} ∪ R(α₂)` for points off
`Γ₁` itself. -/
theorem sidePreserve (S : NestData c) :
    ∃ ρ > 0, ∀ z ∈ Metric.ball S.d.z₁ ρ, z ∉ pairCurve S.P0 →
      (z ∈ pairSide S.P0 ↔ F c z ∈ pairSide S.P0) := by
  obtain ⟨R₁, hR₁⟩ := S.SP
  obtain ⟨rc, hrcpos, hrc⟩ := S.fl.cover R₁
  refine ⟨rc, hrcpos, ?_⟩
  intro z hz hzc
  rw [Metric.mem_ball] at hz
  have hzpos : 0 < ‖z - S.d.z₁‖ := by
    rw [norm_pos_iff]
    intro h
    refine hzc ?_
    rw [sub_eq_zero.mp h, ← S.P0y]
    exact (mem_pairCurve_iff S.P0 S.P0.y).mpr (Or.inr (Or.inl rfl))
  have hzv : ‖z - S.d.z₁‖ < rc := by rwa [dist_eq_norm] at hz
  rcases hrc z hzpos hzv with hPa | ⟨w, hw, hwz⟩
  · have hzin : z ∈ pairSide S.P0 := S.Pa_far hPa
    have hFin : F c z ∈ pairSide S.P0 := S.Pa_far (S.fl.mapsTo_Pa hPa)
    exact ⟨fun _ => hFin, fun _ => hzin⟩
  · rw [← hwz, ← S.fl.Ψ_shift w]
    exact hR₁ w hw

end Work.ELNest

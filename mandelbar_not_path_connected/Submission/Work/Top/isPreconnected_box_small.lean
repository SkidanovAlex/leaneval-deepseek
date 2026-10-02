import Mathlib
import Submission.Work.Top.Defs
import Submission.Work.Top.reIm_box_inter_ball
import Submission.Work.Top.isPreconnected_box_gt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The rotated interior box cut out by `Φ` is preconnected

Under the abstract Nakane interface, `Φ` restricts to a homeomorphism from the complement of `Mb`
onto the exterior disc `{w | 1 < ‖w‖}`.  Fixing an angle `θ`, the map `w ↦ rayRot θ w` is the
rotation of the Böttcher plane by `-2πθ`, and the region

`{c : ℂ | c ∉ Mb ∧ |(rayRot θ (Φ c)).re - R| < a ∧ |(rayRot θ (Φ c)).im| < b ∧ ‖Φ c‖ < R}`

is precisely the preimage, under `c ↦ rayRot θ (Φ c)`, of the box

`B = {w : ℂ | |w.re - R| < a ∧ |w.im| < b ∧ ‖w‖ < R}`,

the horizontal strip of width `2a` centred at `R`, truncated by the open disc of radius `R`.

Since `R - a ≥ 1` (here `a ≤ R - 1`), every point of the strip has real part `> 1`, hence lies
in the exterior disc; the box `B` is convex and therefore preconnected by `reIm_box_inter_ball`.
The rotation `rayRot θ` is a homeomorphism of `ℂ`, so the inverse Böttcher correspondence
`w ↦ (Φ|_{Mbᶜ})⁻¹ (rayRot (-θ) w)` is a continuous map from `B` onto the region; the image of a
preconnected set under a continuous map is preconnected.
-/

namespace Work.Top

open Classical Filter Set
open scoped Topology

theorem isPreconnected_box_small {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ) {θ R a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hR : 1 < R) (haR : a ≤ R - 1) :
    IsPreconnected {c : ℂ | c ∉ Mb ∧ |(Work.Top.rayRot θ (Φ c)).re - R| < a ∧
      |(Work.Top.rayRot θ (Φ c)).im| < b ∧ ‖Φ c‖ < R} := by
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  set B : Set ℂ := {w : ℂ | |w.re - R| < a ∧ |w.im| < b ∧ ‖w‖ < R} with hBdef
  have hBpre : IsPreconnected B := reIm_box_inter_ball ha hb hRpos
  have hBsub : B ⊆ exteriorDisc := fun w hw => by
    rw [mem_exteriorDisc]
    have hre : 1 < w.re := by
      have h := (abs_lt.mp hw.1).1
      linarith
    have hle : w.re ≤ ‖w‖ := le_trans (le_abs_self w.re) (Complex.abs_re_le_norm w)
    linarith
  have hmem : ∀ w : ↥B, rayRot (-θ) (w : ℂ) ∈ exteriorDisc := fun w => by
    rw [mem_exteriorDisc, norm_rayRot]
    exact hBsub w.2
  -- the inverse Böttcher correspondence on the box
  let g : ↥B → ℂ := fun w =>
    ((hN.e.symm (⟨rayRot (-θ) (w : ℂ), hmem w⟩ : ↥exteriorDisc) : ↥Mbᶜ) : ℂ)
  have hgc : Continuous g := by
    have h1 : Continuous fun w : ↥B => (⟨rayRot (-θ) (w : ℂ), hmem w⟩ : ↥exteriorDisc) :=
      Continuous.subtype_mk ((continuous_rayRot (-θ)).comp continuous_subtype_val) hmem
    exact continuous_subtype_val.comp (hN.e.symm.continuous.comp h1)
  have hpreB : PreconnectedSpace ↥B := isPreconnected_iff_preconnectedSpace.mp hBpre
  have hrange : Set.range g = {c : ℂ | c ∉ Mb ∧ |(rayRot θ (Φ c)).re - R| < a ∧
      |(rayRot θ (Φ c)).im| < b ∧ ‖Φ c‖ < R} := by
    ext c
    constructor
    · rintro ⟨w, rfl⟩
      have hc : g w ∉ Mb :=
        (hN.e.symm (⟨rayRot (-θ) (w : ℂ), hmem w⟩ : ↥exteriorDisc) : ↥Mbᶜ).2
      have hPhi : Φ (g w) = rayRot (-θ) (w : ℂ) := by
        rw [hN.he ⟨g w, hc⟩]
        have hx : (⟨g w, hc⟩ : ↥Mbᶜ) =
            hN.e.symm (⟨rayRot (-θ) (w : ℂ), hmem w⟩ : ↥exteriorDisc) := by
          apply Subtype.ext; rfl
        rw [hx, Homeomorph.apply_symm_apply]
      refine ⟨hc, ?_, ?_, ?_⟩
      · rw [hPhi, rayRot_rayRot_neg]; exact w.2.1
      · rw [hPhi, rayRot_rayRot_neg]; exact w.2.2.1
      · rw [hPhi, norm_rayRot]; exact w.2.2.2
    · rintro ⟨hc, h1, h2, h3⟩
      have hwB : rayRot θ (Φ c) ∈ B := ⟨h1, h2, by rw [norm_rayRot]; exact h3⟩
      refine ⟨⟨rayRot θ (Φ c), hwB⟩, ?_⟩
      have hmemw := hmem ⟨rayRot θ (Φ c), hwB⟩
      have heq : rayRot (-θ) (rayRot θ (Φ c)) = Φ c := rayRot_neg_rayRot θ (Φ c)
      have hsub : (⟨rayRot (-θ) (rayRot θ (Φ c)), hmemw⟩ : ↥exteriorDisc)
          = (⟨Φ c, hN.Phi_mem_exteriorDisc hc⟩ : ↥exteriorDisc) := by
        apply Subtype.ext; exact heq
      have he_obj : hN.e ⟨c, hc⟩ = (⟨Φ c, hN.Phi_mem_exteriorDisc hc⟩ : ↥exteriorDisc) := by
        apply Subtype.ext; exact (hN.he ⟨c, hc⟩).symm
      have hy : hN.e.symm (⟨Φ c, hN.Phi_mem_exteriorDisc hc⟩ : ↥exteriorDisc) = ⟨c, hc⟩ := by
        rw [← he_obj, Homeomorph.symm_apply_apply]
      show ((hN.e.symm (⟨rayRot (-θ) (rayRot θ (Φ c)), hmemw⟩ : ↥exteriorDisc) : ↥Mbᶜ) : ℂ) = c
      rw [hsub, hy]
  rw [← hrange]
  exact isPreconnected_range hgc

end Work.Top

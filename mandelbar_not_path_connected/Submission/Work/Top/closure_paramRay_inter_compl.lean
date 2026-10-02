import Mathlib
import Submission.Work.Top.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

namespace Work.Top

/-!
# The closure of a parameter ray, off the connectedness locus

The parameter ray of angle `θ` is the part of the preimage under the Böttcher coordinate `Φ` of the
open radial line `{t e^{2πiθ} : t > 1}` which lies off `Mb`.  Points of `Mb` may of course be
accumulated (the landing points of the ray), but *no other* point is: if `c` is in the closure of
the ray and still off `Mb`, then `Φ c` lies on the *closed* radial line `{t e^{2πiθ} : t ≥ 0}`
(continuity of `Φ` at `c` plus closedness of that line), while `c ∉ Mb` forces `‖Φ c‖ > 1`; hence
`c` already lies on the open ray.

The closed radial line is the zero set of the continuous map `w ↦ w - ‖w‖ e^{2πiθ}`.
-/

/-- The closed radial line of the Böttcher coordinate in direction `θ`, i.e.
`{t e^{2πiθ} : 0 ≤ t}`.  It is described as the set of `w` whose modulus, inserted back into
`rayPoint`, returns `w`. -/
def closedRay (θ : ℝ) : Set ℂ := {w : ℂ | w = NakaneData.rayPoint θ ‖w‖}

theorem isClosed_closedRay (θ : ℝ) : IsClosed (closedRay θ) := by
  have hcont : Continuous (fun w : ℂ => NakaneData.rayPoint θ ‖w‖) := by
    unfold NakaneData.rayPoint
    exact (Complex.continuous_ofReal.comp continuous_norm).mul continuous_const
  exact isClosed_eq continuous_id hcont

namespace NakaneData

variable {Mb : Set ℂ} {Φ : ℂ → ℂ}

/-- The Böttcher coordinate `Φ` is continuous at every point off the connectedness locus: there it
agrees with the homeomorphism `e`. -/
theorem continuousOn_Phi (hN : NakaneData Mb Φ) : ContinuousOn Φ Mbᶜ := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h1 : (Mbᶜ).domRestrict Φ = fun x : ↥Mbᶜ => ((hN.e x : ↥exteriorDisc) : ℂ) := by
    funext x
    exact hN.he x
  rw [h1]
  exact continuous_subtype_val.comp hN.e.continuous

theorem continuousAt_Phi (hN : NakaneData Mb Φ) {c : ℂ} (hc : c ∉ Mb) : ContinuousAt Φ c :=
  hN.continuousOn_Phi.continuousAt (hN.isClosed_mb.isOpen_compl.mem_nhds hc)

end NakaneData

theorem closure_paramRay_inter_compl {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ) (θ : ℝ) :
    closure (Work.Top.NakaneData.paramRay hN θ) ∩ Mbᶜ = Work.Top.NakaneData.paramRay hN θ := by
  apply Set.Subset.antisymm
  · -- The hard inclusion: a point of the closure which is still off `Mb` already lies on the ray.
    intro c hc
    rw [Set.mem_inter_iff] at hc
    obtain ⟨hccl, hcmb⟩ := hc
    have hNB : (𝓝[NakaneData.paramRay hN θ] c).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp hccl
    have htend : Tendsto Φ (𝓝[NakaneData.paramRay hN θ] c) (𝓝 (Φ c)) :=
      (NakaneData.continuousAt_Phi hN hcmb).tendsto.mono_left inf_le_left
    have hev : ∀ᶠ x in 𝓝[NakaneData.paramRay hN θ] c, Φ x ∈ closedRay θ := by
      apply eventually_of_mem self_mem_nhdsWithin
      intro x hx
      obtain ⟨_, t, ht, hxt⟩ := hx
      show Φ x = NakaneData.rayPoint θ ‖Φ x‖
      have hnorm : ‖Φ x‖ = t := by
        rw [hxt, NakaneData.norm_rayPoint, abs_of_pos (by linarith)]
      rw [hnorm, hxt]
    have himg : Φ c ∈ closedRay θ := (isClosed_closedRay θ).mem_of_tendsto htend hev
    exact ⟨hcmb, ‖Φ c‖, hN.Phi_mem_exteriorDisc hcmb, himg⟩
  · -- The ray is contained in its closure and off `Mb`.
    intro c hc
    exact ⟨subset_closure hc, (NakaneData.paramRay_subset_compl hN θ) hc⟩

end Work.Top

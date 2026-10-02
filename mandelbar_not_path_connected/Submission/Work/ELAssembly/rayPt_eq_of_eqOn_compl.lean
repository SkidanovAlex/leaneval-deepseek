import Mathlib
import Submission.Work.Top.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

open Work.Top

/-- If two Böttcher coordinates `Φ₁, Φ₂` of the same connectedness locus `Mb` agree off `Mb`,
then the parameter rays they define are the same: the level-`t` points of the rays agree, and
the limits of the rays (as `t ↓ 1`) agree. -/
theorem rayPt_eq_of_eqOn_compl {Mb : Set ℂ} {Φ₁ Φ₂ : ℂ → ℂ} (hN₁ : Work.Top.NakaneData Mb Φ₁) (hN₂ : Work.Top.NakaneData Mb Φ₂) (h : ∀ z : ℂ, z ∉ Mb → Φ₁ z = Φ₂ z) : (∀ (θ t : ℝ), hN₁.rayPt θ t = hN₂.rayPt θ t) ∧ (∀ (θ : ℝ) (y : ℂ), (Filter.Tendsto (fun t : ℝ => hN₁.rayPt θ t) (nhdsWithin 1 (Set.Ioi 1)) (nhds y) ↔ Filter.Tendsto (fun t : ℝ => hN₂.rayPt θ t) (nhdsWithin 1 (Set.Ioi 1)) (nhds y))) := by
  -- The inverse images of a point of the exterior disc under the two homeomorphisms coincide.
  have key : ∀ (w : ℂ) (hw : w ∈ exteriorDisc),
      ((hN₁.e.symm ⟨w, hw⟩ : ↥Mbᶜ) : ℂ) = ((hN₂.e.symm ⟨w, hw⟩ : ↥Mbᶜ) : ℂ) := by
    intro w hw
    have h1 : Φ₁ ((hN₁.e.symm ⟨w, hw⟩ : ↥Mbᶜ) : ℂ) = w := by
      rw [hN₁.he, Homeomorph.apply_symm_apply]
    have h2 : Φ₂ ((hN₂.e.symm ⟨w, hw⟩ : ↥Mbᶜ) : ℂ) = w := by
      rw [hN₂.he, Homeomorph.apply_symm_apply]
    have hm1 : ((hN₁.e.symm ⟨w, hw⟩ : ↥Mbᶜ) : ℂ) ∈ Mbᶜ := (hN₁.e.symm ⟨w, hw⟩ : ↥Mbᶜ).2
    have hm2 : ((hN₂.e.symm ⟨w, hw⟩ : ↥Mbᶜ) : ℂ) ∈ Mbᶜ := (hN₂.e.symm ⟨w, hw⟩ : ↥Mbᶜ).2
    exact hN₂.injOn_Phi hm1 hm2 (by rw [← h _ hm1, h1, h2])
  have hray : ∀ θ t, hN₁.rayPt θ t = hN₂.rayPt θ t := by
    intro θ t
    by_cases ht : 1 < t
    · rw [NakaneData.rayPt, NakaneData.rayPt, dite_eq_left ht, dite_eq_left ht]
      exact key (NakaneData.rayPoint θ t) (NakaneData.rayPoint_mem_exteriorDisc ht)
    · rw [NakaneData.rayPt, NakaneData.rayPt, dite_eq_right ht, dite_eq_right ht]
  refine ⟨hray, fun θ y => ?_⟩
  have hf : (fun t : ℝ => hN₁.rayPt θ t) = (fun t : ℝ => hN₂.rayPt θ t) := funext (hray θ)
  rw [hf]

end Work.ELAssembly

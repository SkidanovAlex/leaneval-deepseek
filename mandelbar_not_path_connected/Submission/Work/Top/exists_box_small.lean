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

/-- **Small-box property of the inverse Böttcher coordinate.**

If `w₀ = Φ q` lies in the exterior disc, then `Φ` maps points off the connectedness locus
that are close to `q` onto points close to `w₀`, *inversely*: points `c ∉ Mb` with `Φ c` near
`w₀` are near `q`.  (Here `q ∉ Mb` automatically, since `w₀ ≠ 0`.)  This is exactly continuity
of the inverse of the homeomorphism `hN.e` at `⟨w₀, hw₀⟩`. -/
theorem exists_box_small {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ) {q w₀ : ℂ}
    (hq : Φ q = w₀) (hw₀ : w₀ ∈ Work.Top.exteriorDisc) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ c : ℂ, c ∉ Mb → ‖Φ c - w₀‖ < δ → dist c q < ε := by
  have hqM : q ∉ Mb := by
    intro h
    have h0 : Φ q = 0 := hN.Phi_eq_zero_of_mem q h
    rw [h0] at hq
    rw [← hq] at hw₀
    rw [mem_exteriorDisc] at hw₀
    simp at hw₀
    linarith
  have heq : hN.e ⟨q, hqM⟩ = ⟨w₀, hw₀⟩ := by
    apply Subtype.ext
    rw [← hN.he ⟨q, hqM⟩, hq]
  have hcont : ContinuousAt hN.e.symm ⟨w₀, hw₀⟩ := hN.e.symm.continuous.continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hδ'⟩ := hcont ε hε
  refine ⟨δ, hδ, fun c hc hdist => ?_⟩
  have hmem : Φ c ∈ exteriorDisc := mem_exteriorDisc.mpr (hN.Phi_mem_exteriorDisc hc)
  have hy : hN.e ⟨c, hc⟩ = (⟨Φ c, hmem⟩ : ↥exteriorDisc) := by
    apply Subtype.ext
    rw [← hN.he ⟨c, hc⟩]
  have hdist_y : dist (⟨Φ c, hmem⟩ : ↥exteriorDisc) ⟨w₀, hw₀⟩ < δ := by
    rw [Subtype.dist_eq]; rwa [dist_eq_norm]
  have h1 := hδ' (x := ⟨Φ c, hmem⟩) hdist_y
  rw [← heq, Homeomorph.symm_apply_apply] at h1
  have h2 : hN.e.symm (⟨Φ c, hmem⟩ : ↥exteriorDisc) = ⟨c, hc⟩ := by
    rw [← hy, Homeomorph.symm_apply_apply]
  rw [h2, Subtype.dist_eq] at h1
  simpa [dist_eq_norm] using h1

end Work.Top

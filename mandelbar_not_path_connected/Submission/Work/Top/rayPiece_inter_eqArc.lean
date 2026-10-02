import Mathlib
import Submission.Work.Top.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Top

open Set

theorem rayPiece_inter_eqArc {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ)
    {β β₁ β₂ t₀ R : ℝ} (hβ : β ∈ Set.Icc β₁ β₂) (hR : 1 < R) (ht : t₀ ≤ Real.log R) :
    Work.Top.NakaneData.rayPiece hN β t₀ R ∩ Work.Top.NakaneData.eqArc hN β₁ β₂ R
      = {Work.Top.NakaneData.rayPt hN β R} := by
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨⟨⟨?_, ?_, ?_⟩, ⟨⟨β, hβ⟩, rfl⟩⟩, ?_⟩
  · exact ⟨hN.rayPt_notMem hR, R, hR, hN.Phi_rayPt hR⟩
  · rw [hN.potential_rayPt hR]; exact ht
  · rw [hN.potential_rayPt hR]
  · rintro c ⟨hc1, hc2⟩
    obtain ⟨hcnotmem, t, ht1, hΦ⟩ := (hN.mem_paramRay_iff (θ := β) (c := c)).mp hc1.1
    rcases hc2 with ⟨s, hs⟩
    have hΦ' : Φ c = NakaneData.rayPoint s.1 R := by
      rw [← hs, hN.Phi_rayPt hR]
    have htR : t = R := by
      have h1 := congrArg norm (hΦ.symm.trans hΦ')
      rw [NakaneData.norm_rayPoint, NakaneData.norm_rayPoint,
        abs_of_pos (by linarith : (0 : ℝ) < t), abs_of_pos (by linarith : (0 : ℝ) < R)] at h1
      exact h1
    have hfin : Φ c = Φ (NakaneData.rayPt hN β R) := by
      rw [hN.Phi_rayPt hR, hΦ, htR]
    exact hN.injOn_Phi hcnotmem (hN.rayPt_notMem hR) hfin

end Work.Top

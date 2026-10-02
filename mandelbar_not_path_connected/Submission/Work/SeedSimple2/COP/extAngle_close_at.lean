import Mathlib
import Submission.Work.SeedSimple2.Defs
import Submission.Work.Top.extAngle_close_of_Phi_close
import Submission.Work.ELRig.SideFlipChart

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedSimple2.COP

/-- **Generalised local angle continuity** (`COP/NOTES_COP.md` §1): at an interior point `rayPt hN e t₀` (`0 < e < 1`, `t₀ > 1`) of the ray of angle `e`, the external angle `Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ)` is continuous and the point is off the filled Julia set, with the explicit tolerance `η`.

Proof: `rayPt hN e t₀ ∉ K c` (`rayPt_notMem_K`), `dynPhi` is continuous at it (`Work.ELRig.continuousOn_dynPhi`, `K c` closed), `dynPhi (rayPt hN e t₀) = rayPoint e t₀` (`Phi_rayPt`), then apply `Work.Top.extAngle_close_of_Phi_close` (with `Mb := K c`, `Φ := dynPhi c d.φ`). -/
theorem extAngle_close_at {c : ℂ} (d : Work.EL.RootParabolic c)
    {e η : ℝ} (he0 : 0 < e) (he1 : e < 1) (hη : 0 < η) {t₀ : ℝ} (ht₀ : 1 < t₀) :
    ∃ δ > 0, ∀ z : ℂ, ‖z - Work.EL.rayPt d.hN e t₀‖ < δ →
      z ∉ Work.EL.K c ∧
      |Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) z - e| < η := by
  -- the angular tolerance supplied by the abstract parameter-ray lemma
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ :=
    Work.Top.extAngle_close_of_Phi_close (Mb := Work.EL.K c)
      (Φ := Work.EL.dynPhi c d.φ) d.hN he0 he1 ht₀ hη
  -- the reference point is off the filled Julia set, and its Böttcher value is the ray point
  have hpK : Work.EL.rayPt d.hN e t₀ ∉ Work.EL.K c := Work.EL.rayPt_notMem_K d.hN ht₀
  have hpPhi : Work.EL.dynPhi c d.φ (Work.EL.rayPt d.hN e t₀) =
      Work.Top.NakaneData.rayPoint e t₀ := Work.Top.NakaneData.Phi_rayPt d.hN ht₀
  have hpnorm : ‖Work.Top.NakaneData.rayPoint e t₀‖ = t₀ := by
    rw [Work.Top.NakaneData.norm_rayPoint, abs_of_pos (by linarith)]
  -- `dynPhi` is continuous at the reference point, which is off the (closed) filled Julia set
  have hcont : ContinuousAt (Work.EL.dynPhi c d.φ) (Work.EL.rayPt d.hN e t₀) :=
    (Work.ELRig.continuousOn_dynPhi (c := c) (d := d)).continuousAt
      (d.hN.isClosed_mb.isOpen_compl.mem_nhds hpK)
  -- the tolerance is small enough both for the angle and to keep the Böttcher value nonzero
  have hεpos : 0 < min δ₀ t₀ := lt_min hδ₀pos (by linarith)
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont (min δ₀ t₀) hεpos
  refine ⟨δ, hδpos, fun z hz => ?_⟩
  have hd : dist (Work.EL.dynPhi c d.φ z) (Work.EL.dynPhi c d.φ (Work.EL.rayPt d.hN e t₀))
      < min δ₀ t₀ := hδ (by rwa [dist_eq_norm])
  rw [dist_eq_norm, hpPhi] at hd
  -- the Böttcher value stays away from `0`, so `z` is off the filled Julia set
  have hzK : z ∉ Work.EL.K c := by
    intro hzK
    have h0 : Work.EL.dynPhi c d.φ z = 0 := d.hN.Phi_eq_zero_of_mem z hzK
    rw [h0, zero_sub, norm_neg, hpnorm] at hd
    exact absurd (lt_of_lt_of_le hd (min_le_right _ _)) (lt_irrefl t₀)
  refine ⟨hzK, hδ₀ z hzK (lt_of_lt_of_le hd (min_le_left _ _))⟩

end Work.SeedSimple2.COP

import Mathlib
import Submission.Work.Top.Defs
import Submission.Work.Top.paramRay_rayPt_norm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Top

/-- The piece of the parameter ray of angle `β` between the levels `t₀` and `R` is exactly the
image of the interval `[exp t₀, R]` under the parametrisation `t ↦ rayPt hN β t` of that ray.

This is the bridge between the "potential" description of `rayPiece` (a subset of the parameter
ray cut out by `t₀ ≤ potential ≤ log R`) and its "level" description, and it is what makes the
ordering of the points of a ray piece available in the applications. -/
theorem rayPiece_eq_image_Icc {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ)
    {β t₀ R : ℝ} (h₀ : 0 < t₀) (hR : 0 < R) :
    Work.Top.NakaneData.rayPiece hN β t₀ R
      = Work.Top.NakaneData.rayPt hN β '' Set.Icc (Real.exp t₀) R := by
  apply Set.Subset.antisymm
  · -- A point of the ray piece is the ray point at level `‖Φ c‖`, which lies in `[exp t₀, R]`.
    rintro c ⟨hc, h1, h2⟩
    obtain ⟨hc_eq, hpot⟩ := paramRay_rayPt_norm hN hc
    -- the modulus of the Böttcher coordinate of a point of the ray is the level `t > 1`
    obtain ⟨hcMb, t, ht, hΦ⟩ := hc
    have hpos : 0 < ‖Φ c‖ := by
      rw [hΦ, NakaneData.norm_rayPoint, abs_of_pos (by linarith : (0:ℝ) < t)]
      linarith
    have h1' : t₀ ≤ Real.log ‖Φ c‖ := by rw [← hpot]; exact h1
    have h2' : Real.log ‖Φ c‖ ≤ Real.log R := by rw [← hpot]; exact h2
    exact ⟨‖Φ c‖, ⟨(Real.le_log_iff_exp_le hpos).mp h1',
      (Real.log_le_log_iff hpos hR).mp h2'⟩, hc_eq.symm⟩
  · -- Conversely every ray point at a level `t ∈ [exp t₀, R]` lies on the ray piece.
    rintro c ⟨t, ht, rfl⟩
    rw [Set.mem_Icc] at ht
    have ht1 : 1 < t := by
      have : 1 < Real.exp t₀ := Real.one_lt_exp_iff.mpr h₀
      linarith [ht.1]
    have hpos : 0 < t := by linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [NakaneData.mem_paramRay_iff]
      exact ⟨hN.rayPt_notMem ht1, t, ht1, hN.Phi_rayPt ht1⟩
    · rw [NakaneData.potential_rayPt hN ht1]
      exact (Real.le_log_iff_exp_le hpos).mpr ht.1
    · rw [NakaneData.potential_rayPt hN ht1]
      exact Real.log_le_log hpos ht.2

end Work.Top

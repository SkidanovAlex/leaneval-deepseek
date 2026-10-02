import Mathlib
import Submission.Work.Top.Defs
import Submission.Work.Top.Phi_eq_norm_mul_exp_extAngle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Top

/-- A point `c` outside the connectedness locus whose potential is `log R` lies on the
parameter ray of its own external angle at level `R`. -/
theorem rayPt_extAngle {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ) {R : ℝ} {c : ℂ}
    (hR : 1 < R) (hc : c ∉ Mb) (hG : Work.Top.potential Mb Φ c = Real.log R) :
    hN.rayPt (Work.Top.NakaneData.extAngle Φ c) R = c := by
  have hpos : 0 < ‖Φ c‖ := lt_trans zero_lt_one (hN.Phi_mem_exteriorDisc hc)
  have hlog : Real.log ‖Φ c‖ = Real.log R := by
    rw [← hG, potential_of_not_mem hc]
  have hRpos : 0 < R := by linarith
  have hnorm : ‖Φ c‖ = R := by
    rw [← Real.exp_log hpos, ← Real.exp_log hRpos, hlog]
  have hΦ : Φ c = Work.Top.NakaneData.rayPoint (Work.Top.NakaneData.extAngle Φ c) R := by
    rw [Phi_eq_norm_mul_exp_extAngle hN (hN.Phi_ne_zero hc), hnorm]
    rfl
  exact (hN.injOn_Phi hc (hN.rayPt_notMem hR) (hΦ.trans (hN.Phi_rayPt hR).symm)).symm

theorem mem_eqArc_of {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ) {β₁ β₂ R : ℝ} {c : ℂ}
    (hR : 1 < R) (hc : c ∉ Mb) (hG : Work.Top.potential Mb Φ c = Real.log R)
    (hang : Work.Top.NakaneData.extAngle Φ c ∈ Set.Icc β₁ β₂) :
    c ∈ Work.Top.NakaneData.eqArc hN β₁ β₂ R :=
  ⟨⟨Work.Top.NakaneData.extAngle Φ c, hang⟩, rayPt_extAngle hN hR hc hG⟩

end Work.Top

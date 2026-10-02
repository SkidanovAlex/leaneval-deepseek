import Mathlib
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

/-- The points of the parameter ray of angle `θ` escape to infinity with their level: the
potential of `rayPt hN θ t` is `log t` (for `t > 1`), and the potential is continuous with
compact sublevel sets (`NakaneData.tendsto_potential` says the potential tends to `+∞` along
large norm, which -- by continuity -- bounds the potential on every closed ball).  Hence a point
of large potential, in particular a ray point of large level, must have large norm. -/
theorem tendsto_norm_rayPt_atTop {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (θ : ℝ) :
    Filter.Tendsto (fun t : ℝ => ‖Work.EL.rayPt hN θ t‖) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  rcases le_total b 0 with hb | hb
  · exact ⟨1, fun t _ => le_trans hb (norm_nonneg _)⟩
  · have hcont : Continuous (Work.EL.pot hN) := hN.continuous_potential
    have hbdd : BddAbove ((Work.EL.pot hN) '' Metric.closedBall (0 : ℂ) b) :=
      (ProperSpace.isCompact_closedBall (0 : ℂ) b).image hcont |>.bddAbove
    obtain ⟨K, hK⟩ := hbdd
    refine ⟨max 1 (Real.exp K) + 1, fun t ht => ?_⟩
    have ht1 : (1 : ℝ) < t := by
      have : (1 : ℝ) ≤ max 1 (Real.exp K) := le_max_left _ _
      linarith
    by_contra hcon
    rw [not_le] at hcon
    have hmem : Work.EL.rayPt hN θ t ∈ Metric.closedBall (0 : ℂ) b := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt hcon
    have hle : Work.EL.pot hN (Work.EL.rayPt hN θ t) ≤ K := hK ⟨_, hmem, rfl⟩
    rw [Work.EL.pot_rayPt hN ht1] at hle
    have hexp : Real.exp K < t := by
      have : Real.exp K ≤ max 1 (Real.exp K) := le_max_right _ _
      linarith
    have hlt : K < Real.log t := by
      rw [← Real.log_exp K]
      exact Real.log_lt_log (Real.exp_pos K) hexp
    linarith

end Work.LandLeaves

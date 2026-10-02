import Mathlib
import Submission.Work.NAKANE.Defs
import Submission.Work.NAKANE.GreenJoint

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE.BottcherJoint

open Classical Filter Set
open scoped Topology

/-! ## The escape gap

The difference `G_c z - G_c 0` is what the critical domain tests, and what the uniform escape gap
bounds below.  Its joint continuity is immediate from `Work.NAKANE.continuous_greenFun` and
`Work.NAKANE.continuous_paramPotential`. -/

/-- The escape gap of the pair `(c, z)`: `G_c z - G_c 0 = G_c z - paramPotential c`. -/
noncomputable def gapFun (p : ℂ × ℂ) : ℝ :=
  Work.ParamRays.greenFun p.1 p.2 - Work.ParamRays.paramPotential p.1

theorem gapFun_apply (c z : ℂ) :
    gapFun (c, z) = Work.ParamRays.greenFun c z - Work.ParamRays.paramPotential c := rfl

theorem continuous_gapFun : Continuous gapFun :=
  Work.NAKANE.continuous_greenFun.sub
    (Work.NAKANE.continuous_paramPotential.comp continuous_fst)

/-- The escape gap is positive exactly on the critical domain. -/
theorem gapFun_pos_iff {c z : ℂ} :
    0 < gapFun (c, z) ↔ z ∈ Work.ParamRays.critDomain c :=
  Iff.trans sub_pos Iff.rfl

/-- **Uniform escape gap on a compact subset of the critical domain.**  If the compact set `K` is
contained in `critDomain c₀`, then for all parameters close to `c₀` the potential is *uniformly*
larger than `paramPotential c` on `K`: there are `ε > 0` and `s > 0` with
`paramPotential c + s ≤ greenFun c z` for `‖c - c₀‖ < ε` and `z ∈ K`.

Proof: `K × {c₀}` is compact inside the open set `{p | paramPotential p.1 < greenFun p.1 p.2}`
(openness from `Work.NAKANE.continuous_greenFun` and `Work.NAKANE.continuous_paramPotential` in
`Submission/Work/NAKANE/GreenJoint.lean`), so
`IsCompact.exists_cthickening_subset_open` gives a uniform neighbourhood of `K × {c₀}` on which the
gap is positive; take `s` to be (say) half of the minimum of `greenFun c z - paramPotential c` on a
compact neighbourhood (if `K = ∅` any `s > 0` works). -/
theorem exists_gap_of_isCompact {c₀ : ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hKc : ∀ z ∈ K, z ∈ Work.ParamRays.critDomain c₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ s : ℝ, 0 < s ∧ ∀ c : ℂ, ‖c - c₀‖ < ε → ∀ z ∈ K,
      Work.ParamRays.paramPotential c + s ≤ Work.ParamRays.greenFun c z := by
  rcases K.eq_empty_or_nonempty with hKe | hne
  · refine ⟨1, one_pos, 1, one_pos, ?_⟩
    intro c _ z hz
    rw [hKe] at hz
    exact absurd hz (Set.notMem_empty z)
  · obtain ⟨z₁, hz₁⟩ := hne
    -- the compact set `{c₀} × K` of pairs
    have hC : IsCompact ({c₀} ×ˢ K : Set (ℂ × ℂ)) := isCompact_singleton.prod hK
    have hCne : ({c₀} ×ˢ K : Set (ℂ × ℂ)).Nonempty := ⟨(c₀, z₁), by simpa using hz₁⟩
    obtain ⟨p₀, hp₀C, hp₀min⟩ := hC.exists_isMinOn hCne continuous_gapFun.continuousOn
    have hp₀min' : ∀ q ∈ ({c₀} ×ˢ K : Set (ℂ × ℂ)), gapFun p₀ ≤ gapFun q :=
      (isMinOn_iff.mp hp₀min)
    have hp₀1 : p₀.1 = c₀ := hp₀C.1
    have hp₀2 : p₀.2 ∈ K := hp₀C.2
    -- the minimum of the gap over `{c₀} × K` is positive
    have hm : 0 < gapFun p₀ := by
      have hcrit : Work.ParamRays.paramPotential c₀ < Work.ParamRays.greenFun c₀ p₀.2 :=
        hKc p₀.2 hp₀2
      simp only [gapFun, hp₀1]
      linarith
    -- uniform continuity of the gap on the compact box `closedBall c₀ 1 × K`
    have hD : IsCompact ((Metric.closedBall c₀ 1) ×ˢ K : Set (ℂ × ℂ)) :=
      (isCompact_closedBall c₀ 1).prod hK
    have huc : UniformContinuousOn gapFun ((Metric.closedBall c₀ 1) ×ˢ K) :=
      hD.uniformContinuousOn_of_continuous continuous_gapFun.continuousOn
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨δ, hδpos, hδ⟩ := huc (gapFun p₀ / 2) (by linarith)
    refine ⟨min δ 1, lt_min hδpos one_pos, gapFun p₀ / 2, by linarith, ?_⟩
    intro c hc z hz
    have hcδ : ‖c - c₀‖ < δ := lt_of_lt_of_le hc (min_le_left _ _)
    have hc1 : ‖c - c₀‖ < 1 := lt_of_lt_of_le hc (min_le_right _ _)
    have hx : (c, z) ∈ (Metric.closedBall c₀ 1) ×ˢ K := by
      refine ⟨?_, hz⟩
      rw [Metric.mem_closedBall, dist_eq_norm]
      linarith
    have hy : (c₀, z) ∈ (Metric.closedBall c₀ 1) ×ˢ K := by
      refine ⟨?_, hz⟩
      rw [Metric.mem_closedBall, dist_eq_norm]
      simp
    have hxy : dist (c, z) (c₀, z) < δ := by
      rw [Prod.dist_eq, dist_self, max_lt_iff]
      exact ⟨by rwa [dist_eq_norm], hδpos⟩
    have hgap := hδ (c, z) hx (c₀, z) hy hxy
    rw [Real.dist_eq] at hgap
    have hmin : gapFun p₀ ≤ gapFun (c₀, z) := hp₀min' (c₀, z) (by simp [hz])
    have hkey : gapFun p₀ / 2 ≤ gapFun (c, z) := by
      have h1 : gapFun (c₀, z) - gapFun (c, z) ≤ |gapFun (c, z) - gapFun (c₀, z)| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      linarith
    have hcz : gapFun (c, z) = Work.ParamRays.greenFun c z - Work.ParamRays.paramPotential c :=
      gapFun_apply c z
    linarith

end Work.NAKANE.BottcherJoint

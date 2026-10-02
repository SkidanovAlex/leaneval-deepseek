/-
Copyright: subproject `Submission/Work/PARIMPL2/Lavaurs/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.Lavaurs.gtc_uniform_close` — joint uniform continuity of `gtc` over a
compact set of `w`

`gtc c = (T_c)^[5]` is the antiholomorphic square root of the second return map
`Ft c = (T_c)^[10]`, uncurried continuous in `(c, z)`
(`Work.PARIMPL.continuous_uncurry_gtc`).  This file extracts the quantitative form of that
continuity that the Lavaurs endgame needs: **one** radius `r` controls simultaneously the
parameter perturbation `‖c − c₀‖ < r` and the perturbation `‖z − w‖ < r` of the evaluation
point, uniformly for `w` ranging over a compact set `K'`.

The proof is Heine–Cantor on a compact rectangle: `gtc` restricted to the compact set
`closedBall c₀ 1 ×ˢ closedBall 0 (R + 1)` (where `K' ⊆ closedBall 0 R`) is uniformly
continuous, and both pairs `(c, z)` and `(c₀, w)` lie in that rectangle as soon as
`‖c − c₀‖ < 1` and `‖z − w‖ < 1`.
-/
import Mathlib
import Submission.Work.PARIMPL.Nm_mem_closure

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Lavaurs

open Metric

/-- **Joint uniform continuity of `gtc` near `(c₀, K')`.**  For a compact set `K'` of evaluation
points and `ε > 0` there is a radius `r > 0` such that whenever the parameters satisfy
`‖c − c₀‖ < r`, the point `w` ranges over `K'` and `z` is within `r` of `w`, the values
`gtc c z` and `gtc c₀ w` differ by less than `ε`. -/
theorem gtc_uniform_close {c₀ : ℂ} {K' : Set ℂ} (hK' : IsCompact K')
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ c : ℂ, ‖c - c₀‖ < r → ∀ w ∈ K', ∀ z : ℂ, ‖z - w‖ < r →
      ‖Work.PARIMPL.gtc c z - Work.PARIMPL.gtc c₀ w‖ < ε := by
  -- a radius containing `K'`
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hK'.isBounded
  -- the uncurried fifth iterate is continuous
  have hG : Continuous fun q : ℂ × ℂ => Work.PARIMPL.gtc q.1 q.2 :=
    Work.PARIMPL.continuous_uncurry_gtc
  -- on the compact rectangle `closedBall c₀ 1 × closedBall 0 (R + 1)` it is uniformly continuous
  have hS : IsCompact (Metric.closedBall c₀ 1 ×ˢ Metric.closedBall (0 : ℂ) (R + 1)) :=
    (isCompact_closedBall c₀ 1).prod (isCompact_closedBall 0 (R + 1))
  have hunif := hS.uniformContinuousOn_of_continuous hG.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hunif
  obtain ⟨δ, hδpos, hδ⟩ := hunif ε hε
  refine ⟨min δ 1, lt_min hδpos one_pos, ?_⟩
  intro c hc w hw z hz
  have hc1 : ‖c - c₀‖ < 1 := lt_of_lt_of_le hc (min_le_right _ _)
  have hcd : ‖c - c₀‖ < δ := lt_of_lt_of_le hc (min_le_left _ _)
  have hzw1 : ‖z - w‖ < 1 := lt_of_lt_of_le hz (min_le_right _ _)
  have hzwd : ‖z - w‖ < δ := lt_of_lt_of_le hz (min_le_left _ _)
  have hwR : ‖w‖ ≤ R := by
    have h := hR hw
    simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using h
  -- `(c, z)` lies in the rectangle
  have hmem1 : (c, z) ∈ Metric.closedBall c₀ 1 ×ˢ Metric.closedBall (0 : ℂ) (R + 1) := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm]; exact le_of_lt hc1
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      have : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
        calc ‖z‖ = ‖(z - w) + w‖ := by ring_nf
          _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
      linarith
  -- `(c₀, w)` lies in the rectangle
  have hmem2 : (c₀, w) ∈ Metric.closedBall c₀ 1 ×ˢ Metric.closedBall (0 : ℂ) (R + 1) := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm]; simp
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; linarith
  have hdist : dist (c, z) (c₀, w) < δ := by
    rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm]
    exact max_lt hcd hzwd
  have hfin := hδ (c, z) hmem1 (c₀, w) hmem2 hdist
  simpa [dist_eq_norm] using hfin

end Work.PARIMPL2.Lavaurs

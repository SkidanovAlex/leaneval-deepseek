import Mathlib
import Submission.Work.PARIMPL.Transit

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.D1

open Metric

/-- **Uniform closeness of `N`-fold iterates of `Ft` on a ball.**  For every `ε > 0` there is a
`ρ > 0` such that whenever the parameters `e` and `c₀` are within `ρ`, the `N`-fold iterates of
`Ft e` and `Ft c₀` differ by at most `ε` on the closed ball of radius `B`.

The mathematical content is only that `(c, z) ↦ (Ft c)^[N] z` is *jointly* continuous (which
`Work.PARIMPL.continuous_orbit_pair` supplies, `Ft` being a polynomial in `(c, z)`): on the
compact product `closedBall c₀ 1 × closedBall 0 B` a continuous map is uniformly continuous. -/
theorem close_iterate_on_ball {c₀ : ℂ} (N : ℕ) (B : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ e : ℂ, ‖e - c₀‖ < ρ →
      ∀ z : ℂ, ‖z‖ ≤ B →
        ‖(Work.PARIMPL.Ft e)^[N] z - (Work.PARIMPL.Ft c₀)^[N] z‖ ≤ ε := by
  intro ε hε
  have hcont : Continuous (fun p : ℂ × ℂ => ((Work.PARIMPL.Ft p.1)^[N]) p.2) :=
    Work.PARIMPL.continuous_orbit_pair N
  have hK : IsCompact (closedBall c₀ (1 : ℝ) ×ˢ closedBall (0 : ℂ) B) :=
    (isCompact_closedBall c₀ 1).prod (isCompact_closedBall 0 B)
  have huc := hK.uniformContinuousOn_of_continuous hcont.continuousOn
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.uniformContinuousOn_iff_le.1 huc) ε hε
  refine ⟨min δ 1, lt_min hδpos one_pos, ?_⟩
  intro e he z hz
  have he1 : e ∈ closedBall c₀ (1 : ℝ) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact le_of_lt (lt_of_lt_of_le he (min_le_right _ _))
  have hzB : z ∈ closedBall (0 : ℂ) B := by
    rw [Metric.mem_closedBall]
    simpa using hz
  have hx : (e, z) ∈ closedBall c₀ 1 ×ˢ closedBall (0 : ℂ) B := ⟨he1, hzB⟩
  have hy : (c₀, z) ∈ closedBall c₀ 1 ×ˢ closedBall (0 : ℂ) B :=
    ⟨Metric.mem_closedBall_self (by norm_num), hzB⟩
  have hdist : dist (e, z) (c₀, z) ≤ min δ 1 := by
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, dist_eq_norm]
    exact le_of_lt he
  have hmain := hδ (e, z) hx (c₀, z) hy (le_trans hdist (min_le_left _ _))
  simpa [dist_eq_norm] using hmain

end Work.GATE2.D1

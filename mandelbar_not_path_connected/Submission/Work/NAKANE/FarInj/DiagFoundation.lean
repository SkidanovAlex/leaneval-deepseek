/-
# Foundation for the diagonal Lipschitz estimate of the Böttcher series

The Böttcher series of the tricorn map is

`bottcherSeries c z = Σ_n 4^{-(n+1)} log (normFactor c ((pMap c)^[n] z))`,
`normFactor c w = pMap c w / w^4`, `pMap c w = (w² + c̄)² + c`.

This file collects the elementary estimates on which the *diagonal* Lipschitz
estimate `‖bottcherSeries x x - bottcherSeries y y‖ ≤ C ‖x - y‖ / ‖x‖²` rests.
Here the parameter `c = x` and the point `x` are of comparable size, so the
far-region lemmas of `Work.Bottcher.Contraction` (which need `‖z‖ ≫ ‖c‖`) do
not apply; instead we use the *exact* expansion

`normFactor c z - 1 = 2 c̄ / z² + (c̄² + c) / z⁴`   (`normFactor_sub_one`)

which is valid as soon as `z ≠ 0`, and the one-step growth of `pMap` in the
diagonal regime `‖c‖ ≤ 2‖w‖` (`norm_pMap_ge`): one iterate of `pMap c` at least
squares the norm.
-/
import Mathlib
import Submission.Work.Bottcher.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped ComplexConjugate Topology
open Work.Bottcher

namespace Work.NAKANE.FarInj

set_option autoImplicit false

noncomputable section

/-! ## The exact expansion of the normalised factor -/

/-- **Exact expansion of `normFactor`.**  For `z ≠ 0`,
`normFactor c z - 1 = 2 c̄ / z² + (c̄² + c) / z⁴`. -/
lemma normFactor_sub_one (c z : ℂ) (hz : z ≠ 0) :
    normFactor c z - 1 = 2 * conj c / z ^ 2 + ((conj c) ^ 2 + c) / z ^ 4 := by
  rw [normFactor, pMap_apply]
  field_simp
  ring

/-! ## One-step growth of `pMap` in the diagonal regime -/

/-- **One-step growth.**  If `16 ≤ ‖w‖` and `‖c‖ ≤ 2‖w‖` (so in particular the
parameter is not much larger than the point) then
`‖w‖⁴ / 2 ≤ ‖pMap c w‖` and `‖w‖ ≤ ‖pMap c w‖`. -/
lemma norm_pMap_ge (c w : ℂ) (hw : 16 ≤ ‖w‖) (hc : ‖c‖ ≤ 2 * ‖w‖) :
    ‖w‖ ^ 4 / 2 ≤ ‖pMap c w‖ ∧ ‖w‖ ≤ ‖pMap c w‖ := by
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hcw : ‖c‖ ≤ ‖w‖ ^ 2 := by nlinarith
  have h1 : ‖w‖ ^ 2 - ‖c‖ ≤ ‖w ^ 2 + conj c‖ := by
    have h := norm_sub_norm_le (w ^ 2) (-(conj c))
    rw [sub_neg_eq_add, norm_neg, Complex.norm_conj, norm_pow] at h
    exact h
  have h1' : (0 : ℝ) ≤ ‖w‖ ^ 2 - ‖c‖ := by linarith
  have h2 : (‖w‖ ^ 2 - ‖c‖) ^ 2 ≤ ‖(w ^ 2 + conj c) ^ 2‖ := by
    rw [norm_pow]
    exact pow_le_pow_left₀ h1' h1 2
  have h4 : ‖(w ^ 2 + conj c) ^ 2‖ - ‖c‖ ≤ ‖pMap c w‖ := by
    have h := norm_sub_norm_le ((w ^ 2 + conj c) ^ 2) (-c)
    rw [norm_neg] at h
    rwa [show (w ^ 2 + conj c) ^ 2 - -c = pMap c w from by rw [pMap_apply, sub_neg_eq_add]] at h
  have h5 : (‖w‖ ^ 2 - 2 * ‖w‖) ^ 2 ≤ (‖w‖ ^ 2 - ‖c‖) ^ 2 := by
    have h6 : 2 * ‖w‖ ≤ ‖w‖ ^ 2 := by nlinarith
    have h7 : ‖w‖ ^ 2 - 2 * ‖w‖ ≤ ‖w‖ ^ 2 - ‖c‖ := by linarith
    exact pow_le_pow_left₀ (by linarith) h7 2
  have h9 : 49 / 64 * ‖w‖ ^ 4 ≤ (‖w‖ ^ 2 - 2 * ‖w‖) ^ 2 := by
    have hwne : ‖w‖ ≠ 0 := by linarith
    have hident : (‖w‖ ^ 2 - 2 * ‖w‖) ^ 2 = ‖w‖ ^ 4 * (1 - 2 / ‖w‖) ^ 2 := by
      field_simp
    rw [hident]
    have h12 : (2 : ℝ) / ‖w‖ ≤ 1 / 8 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖w‖)]
      linarith
    have h13 : (7 / 8 : ℝ) ≤ 1 - 2 / ‖w‖ := by linarith
    have h14 : ((7 / 8 : ℝ)) ^ 2 ≤ (1 - 2 / ‖w‖) ^ 2 := pow_le_pow_left₀ (by norm_num) h13 2
    nlinarith [h14, show (0 : ℝ) ≤ ‖w‖ ^ 4 by positivity]
  have hlow : ‖w‖ ^ 4 / 2 ≤ ‖pMap c w‖ := by
    have h16 : ‖w‖ ^ 4 / 2 ≤ 49 / 64 * ‖w‖ ^ 4 - 2 * ‖w‖ := by
      nlinarith [show (0 : ℝ) ≤ ‖w‖ by linarith, show (4 : ℝ) ≤ ‖w‖ ^ 3 by nlinarith]
    linarith [h16, h9, h5, h2, h4, hcw]
  refine ⟨hlow, ?_⟩
  nlinarith [hlow, show (2 : ℝ) ≤ ‖w‖ ^ 3 by nlinarith, show (0 : ℝ) ≤ ‖w‖ by linarith]

/-! ## The orbits of `pMap x` from `x` and of `pMap y` from `y` stay large -/

/-- **The two orbits stay large.**  For `‖x‖ ≥ 256` and `‖y - x‖ ≤ ‖x‖/2` both
the `pMap x`-orbit of `x` and the `pMap y`-orbit of `y` stay of norm `≥ 16`, and
each stays of norm at least that of its starting point. -/
lemma orbit_bounds (x y : ℂ) (hA : 256 ≤ ‖x‖) (hδ : ‖y - x‖ ≤ ‖x‖ / 2) (n : ℕ) :
    16 ≤ ‖(pMap x)^[n] x‖ ∧ 16 ≤ ‖(pMap y)^[n] y‖ ∧
      ‖x‖ ≤ ‖(pMap x)^[n] x‖ ∧ ‖y‖ ≤ ‖(pMap y)^[n] y‖ := by
  have hAx : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hyl : ‖y‖ ≤ 3 * ‖x‖ / 2 := by
    have h := norm_sub_norm_le y x
    linarith
  have hyg : ‖x‖ / 2 ≤ ‖y‖ := by
    have h := norm_sub_norm_le x y
    rw [norm_sub_rev y x] at hδ
    linarith
  have hAy : 16 ≤ ‖y‖ := by linarith
  induction n with
  | zero =>
      simp only [Function.iterate_zero_apply]
      exact ⟨by linarith, hAy, le_rfl, le_rfl⟩
  | succ n ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      have hc1 : ‖x‖ ≤ 2 * ‖(pMap x)^[n] x‖ := by linarith
      have hc2 : ‖y‖ ≤ 2 * ‖(pMap y)^[n] y‖ := by linarith
      obtain ⟨g1, g2⟩ := norm_pMap_ge x ((pMap x)^[n] x) h1 hc1
      obtain ⟨g3, g4⟩ := norm_pMap_ge y ((pMap y)^[n] y) h2 hc2
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hz0 : (0 : ℝ) ≤ ‖(pMap x)^[n] x‖ := norm_nonneg _
      have hw0 : (0 : ℝ) ≤ ‖(pMap y)^[n] y‖ := norm_nonneg _
      have e1 : (16 : ℝ) ≤ ‖(pMap x)^[n] x‖ ^ 4 / 2 := by
        have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (16 : ℝ)) h1 4
        rw [show ((16 : ℝ)) ^ 4 = 65536 by norm_num] at hp
        linarith
      have e2 : (16 : ℝ) ≤ ‖(pMap y)^[n] y‖ ^ 4 / 2 := by
        have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (16 : ℝ)) h2 4
        rw [show ((16 : ℝ)) ^ 4 = 65536 by norm_num] at hp
        linarith
      exact ⟨le_trans e1 g1, le_trans e2 g3, le_trans h3 g2, le_trans h4 g4⟩

/-! ## `Complex.log` is `2`-Lipschitz on the closed ball of radius `1/2` around `1` -/

/-- **Lipschitz continuity of `log` near `1`.**  If `‖a - 1‖ ≤ 1/2` and
`‖b - 1‖ ≤ 1/2` then `‖log a - log b‖ ≤ 2 ‖a - b‖`. -/
lemma norm_log_sub_log_le {a b : ℂ} (ha : ‖a - 1‖ ≤ 1 / 2) (hb : ‖b - 1‖ ≤ 1 / 2) :
    ‖Complex.log a - Complex.log b‖ ≤ 2 * ‖a - b‖ := by
  have hsa : a ∈ Metric.closedBall (1 : ℂ) (1 / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact ha
  have hsb : b ∈ Metric.closedBall (1 : ℂ) (1 / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hb
  have hs : Convex ℝ (Metric.closedBall (1 : ℂ) (1 / 2)) := convex_closedBall _ _
  have hsub : Metric.closedBall (1 : ℂ) (1 / 2) ⊆ Complex.slitPlane := fun z hz =>
    Complex.ball_one_subset_slitPlane (by
      rw [Metric.mem_ball, dist_eq_norm]
      have h := Metric.mem_closedBall.mp hz
      rw [dist_eq_norm] at h
      linarith)
  have hderiv : ∀ z ∈ Metric.closedBall (1 : ℂ) (1 / 2),
      HasFDerivWithinAt Complex.log (ContinuousLinearMap.toSpanSingleton ℂ z⁻¹)
        (Metric.closedBall (1 : ℂ) (1 / 2)) z := fun z hz =>
    ((Complex.hasDerivAt_log (hsub hz)).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ z ∈ Metric.closedBall (1 : ℂ) (1 / 2),
      ‖ContinuousLinearMap.toSpanSingleton ℂ z⁻¹‖ ≤ 2 := by
    intro z hz
    rw [ContinuousLinearMap.norm_toSpanSingleton]
    have hz1 : ‖z - 1‖ ≤ 1 / 2 := by
      have h := Metric.mem_closedBall.mp hz
      rw [dist_eq_norm] at h
      exact h
    have h1 : (1 : ℝ) / 2 ≤ ‖z‖ := by
      have h2 := norm_sub_norm_le (1 : ℂ) z
      rw [norm_one, norm_sub_rev] at h2
      linarith
    have h2 : (0 : ℝ) < ‖z‖ := by linarith
    rw [norm_inv, inv_le_iff_one_le_mul₀ h2]
    linarith
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbound hs hsa hsb
  simpa only [norm_sub_rev] using h

end

end Work.NAKANE.FarInj

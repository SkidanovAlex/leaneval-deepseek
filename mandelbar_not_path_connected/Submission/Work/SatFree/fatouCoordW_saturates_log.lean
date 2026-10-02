import Mathlib
import Submission.Work.SatFree.Defs
import Submission.Work.GATE2.PL.fatouCoordW_saturates_petal
import Submission.Work.FatouCoord.Main
import Submission.Work.FatouCoord.Exist.fatouCoordW_image_bdd

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SatFree

open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section

/-- **The chart Fatou coordinate saturates a right half-plane up to a logarithmic slack.**

Sign-free version of `Work.GATE2.PL.fatouCoordW_saturates_petal`: the hypothesis `a.re < 1`
is dropped, at the price of the threshold `logSlack K X τ = X + K * (log (1 + ‖τ‖) + π)`.

Setting: `ParabolicBounds f h a r A A'` is `f z = z + z² h z` on `ball 0 r` with
`h z = 1 + a z + O(z²)`, and `ψ = fatouCoordW f (1 - a)` is asymptotic to
`w - (1 - a) * Complex.log w`.

Proof: copy the old proof (unique level point `t s` with `(ψ (s + i t s)).im = τ.im`, continuity
and linear growth of `F s = (ψ (s + i t s)).re`, IVT), replacing the bound
`Work.GATE2.PL.re_le_of_norm_sub` (which needs `0 ≤ (1-a).re`) by the sign-free
`(ψ w).re ≤ w.re + ‖1-a‖ * (log (1 + ‖w‖) + π) + K / w.re` for `Re w ≥ 1`, and using that the
level point `w₀ = s₀ + i t s₀` satisfies `log (1 + ‖w₀‖) ≤ log (1 + ‖τ‖) + O(1)` (obtained by
bootstrapping `‖w₀‖ ≤ ‖τ‖ + ‖1-a‖ * log (1 + ‖w₀‖) + O(1)`, which itself comes from
`Im ψ w₀ = Im τ` together with `|Im (ψ w - w)| ≤ ‖1-a‖ * (log (1 + ‖w‖) + π) + K / w.re`).
The two quantitative conjuncts are what `SatFree.germ_flowerFix_wideSat` consumes. -/
theorem fatouCoordW_saturates_log {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') (Mh : ℝ) :
    ∃ X K : ℝ, 0 ≤ K ∧ ∀ τ : ℂ, Work.SatFree.logSlack K X τ < τ.re →
      ∃ w : ℂ, Mh < w.re ∧ Work.FatouCoord.fatouCoordW f (1 - a) w = τ ∧
        τ.re - Work.SatFree.logSlack K X τ ≤ w.re ∧
        |τ.im| - Work.SatFree.logSlack K X τ ≤ |w.im| := by
  obtain ⟨Nd, hNdpos, hNdr, hdiffd⟩ := Work.FatouCoord.Exist.fatouCoordW_differentiable hb
  obtain ⟨Nc, hNcpos, hNcr, hderc⟩ := Work.FatouCoord.Exist.fatouCoordW_deriv_close hb
  obtain ⟨Nb, K₁, hNbpos, hNbr, hK₁nn, hbdd⟩ := Work.FatouCoord.Exist.fatouCoordW_tsum_bound hb
  set N : ℝ := max (max Nd Nc) Nb + 1 with hNdef
  have hNdN : Nd < N := by
    have h : Nd ≤ max (max Nd Nc) Nb := le_trans (le_max_left _ _) (le_max_left _ _)
    rw [hNdef]; linarith
  have hNcN : Nc < N := by
    have h : Nc ≤ max (max Nd Nc) Nb := le_trans (le_max_right _ _) (le_max_left _ _)
    rw [hNdef]; linarith
  have hNbN : Nb < N := by
    have h : Nb ≤ max (max Nd Nc) Nb := le_max_right _ _
    rw [hNdef]; linarith
  have hN1 : (1 : ℝ) < N := by
    have h : 0 < max (max Nd Nc) Nb :=
      lt_of_lt_of_le hNdpos (le_trans (le_max_left _ _) (le_max_left _ _))
    rw [hNdef]; linarith
  set C : ℝ := ‖(1 : ℂ) - a‖ with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; exact norm_nonneg _
  set c₁ : ℝ := 2 * C + 4 with hc₁def
  set c₂ : ℝ := 2 * C * Real.pi + 4 * K₁ + 100 with hc₂def
  have hc₁pos : 0 < c₁ := by rw [hc₁def]; linarith
  have hc₂pos : 0 < c₂ := by
    rw [hc₂def]
    have h1 : 0 ≤ C * Real.pi := mul_nonneg hCnn Real.pi_pos.le
    linarith
  set X : ℝ := c₂ + max N Mh + 1 with hXdef
  have hX1 : (1 : ℝ) < X := by
    have hNM : N ≤ max N Mh := le_max_left N Mh
    rw [hXdef]; linarith
  refine ⟨X, c₁, hc₁pos.le, ?_⟩
  intro τ hτ
  rw [logSlack_apply] at hτ
  -- hτ : X + c₁ * (Real.log (1 + ‖τ‖) + Real.pi) < τ.re
  have hτX : X < τ.re := by
    have h0 : 0 ≤ Real.log (1 + ‖τ‖) + Real.pi :=
      add_nonneg (Real.log_nonneg (by linarith [norm_nonneg τ])) Real.pi_pos.le
    have h1 : 0 ≤ c₁ * (Real.log (1 + ‖τ‖) + Real.pi) := mul_nonneg hc₁pos.le h0
    linarith
  have hτ1 : (1 : ℝ) < τ.re := lt_trans hX1 hτX
  have hτpos : 0 < τ.re := lt_trans one_pos hτ1
  have hnormτ_ge1 : 1 ≤ ‖τ‖ := le_trans hτ1.le (Complex.re_le_norm τ)
  have hnormτ_pos : 0 < ‖τ‖ := lt_of_lt_of_le one_pos hnormτ_ge1
  have hlognormτ_nn : 0 ≤ Real.log ‖τ‖ := Real.log_nonneg hnormτ_ge1
  have hτN : N < τ.re := by
    have hNM : N ≤ max N Mh := le_max_left N Mh
    rw [hXdef] at hτX
    linarith
  -- the threshold `ρ` for the contraction
  set ρ : ℝ := c₁ * Real.log ‖τ‖ + c₂ with hρdef
  have hρpos : 0 < ρ := by
    have h : 0 ≤ c₁ * Real.log ‖τ‖ := mul_nonneg hc₁pos.le hlognormτ_nn
    rw [hρdef]; linarith
  have hlogSlack_ge : ρ + max N Mh + 1 ≤ X + c₁ * (Real.log (1 + ‖τ‖) + Real.pi) := by
    have h1 : Real.log ‖τ‖ ≤ Real.log (1 + ‖τ‖) :=
      Real.log_le_log hnormτ_pos (by linarith [norm_nonneg τ])
    have h1' : Real.log ‖τ‖ ≤ Real.log (1 + ‖τ‖) + Real.pi := by linarith [Real.pi_pos]
    have h2 : c₁ * Real.log ‖τ‖ ≤ c₁ * (Real.log (1 + ‖τ‖) + Real.pi) :=
      mul_le_mul_of_nonneg_left h1' hc₁pos.le
    rw [hρdef, hXdef]
    linarith
  have hρ_lt_logSlack : ρ < X + c₁ * (Real.log (1 + ‖τ‖) + Real.pi) := by
    have hNM : 0 < max N Mh + 1 := by
      have h : (1 : ℝ) ≤ max N Mh := le_trans hN1.le (le_max_left N Mh)
      linarith
    linarith [hlogSlack_ge]
  have hρ_lt_τ : ρ + max N Mh < τ.re := by
    have h := hlogSlack_ge
    linarith [hτ]
  -- `ψ τ` is within `ρ / 2` of `τ`
  have hKbd : ‖Work.FatouCoord.fatouCoordW f (1 - a) τ
      - Work.FatouCoord.approxCoord (1 - a) τ‖ ≤ K₁ / τ.re :=
    hbdd τ (lt_trans hNbN hτN)
  have hsplit : Work.FatouCoord.fatouCoordW f (1 - a) τ - τ
      = (Work.FatouCoord.approxCoord (1 - a) τ - τ)
        + (Work.FatouCoord.fatouCoordW f (1 - a) τ
          - Work.FatouCoord.approxCoord (1 - a) τ) := by ring
  have hlinterm : Work.FatouCoord.approxCoord (1 - a) τ - τ = -((1 - a) * Complex.log τ) := by
    rw [Work.FatouCoord.approxCoord_apply]; ring
  have hbound1 : ‖Work.FatouCoord.fatouCoordW f (1 - a) τ - τ‖
      ≤ C * ‖Complex.log τ‖ + K₁ / τ.re := by
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    rw [hlinterm, norm_neg, norm_mul, ← hCdef]
    linarith
  have hnormlogτ : ‖Complex.log τ‖ ≤ Real.log ‖τ‖ + Real.pi :=
    Work.FatouCoord.Exist.norm_log_le τ hnormτ_ge1
  have hKdiv : K₁ / τ.re ≤ K₁ := by
    rw [div_le_iff₀ hτpos]
    nlinarith [hK₁nn, hτ1]
  have hcK : C * ‖Complex.log τ‖ + K₁ / τ.re
      ≤ C * (Real.log ‖τ‖ + Real.pi) + K₁ := by
    have h := mul_le_mul_of_nonneg_left hnormlogτ hCnn
    linarith
  have hclog : C * (Real.log ‖τ‖ + Real.pi) + K₁ ≤ ρ / 2 := by
    rw [hρdef, hc₁def, hc₂def]
    nlinarith [hlognormτ_nn, hCnn, hK₁nn]
  have hclose : dist (Work.FatouCoord.fatouCoordW f (1 - a) τ) τ ≤ (1 - (1 / 2 : ℝ)) * ρ := by
    have h : ‖Work.FatouCoord.fatouCoordW f (1 - a) τ - τ‖ ≤ ρ / 2 :=
      le_trans (le_trans hbound1 hcK) hclog
    rw [dist_eq_norm]
    linarith
  -- every point of the ball has large real part
  have hre_ge : ∀ w : ℂ, dist w τ ≤ ρ → τ.re - ρ ≤ w.re := by
    intro w hw
    have h1 : |(τ - w).re| ≤ ‖τ - w‖ := Complex.abs_re_le_norm _
    have h2 : (τ - w).re = τ.re - w.re := by simp
    have h3 : ‖τ - w‖ = dist w τ := by rw [dist_eq_norm, norm_sub_rev]
    rw [h2] at h1
    have h4 : (τ.re - w.re) ≤ |τ.re - w.re| := le_abs_self _
    have h5 : ‖τ - w‖ ≤ ρ := by rw [h3]; exact hw
    linarith
  have hdiff_ball : ∀ w : ℂ, dist w τ ≤ ρ →
      DifferentiableAt ℂ (Work.FatouCoord.fatouCoordW f (1 - a)) w := by
    intro w hw
    have hwre : Nd < w.re := by
      have h1 := hre_ge w hw
      have hNM : N ≤ max N Mh := le_max_left N Mh
      linarith
    exact (hdiffd w hwre).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hwre)
  have hbound_ball : ∀ w : ℂ, dist w τ ≤ ρ →
      ‖deriv (Work.FatouCoord.fatouCoordW f (1 - a)) w - 1‖ ≤ 1 / 2 := by
    intro w hw
    have hwre : Nc < w.re := by
      have h1 := hre_ge w hw
      have hNM : N ≤ max N Mh := le_max_left N Mh
      linarith
    exact hderc w hwre
  obtain ⟨w, hwρ, hwψ⟩ := Work.FatouCoord.Exist.exists_eq_of_deriv_close
    (ψ := Work.FatouCoord.fatouCoordW f (1 - a)) (τ := τ) (ρ := ρ) (q := 1 / 2)
    hρpos (by norm_num) (by norm_num) hdiff_ball hbound_ball hclose
  refine ⟨w, ?_, hwψ, ?_, ?_⟩
  · -- `Mh < w.re`
    have h1 := hre_ge w hwρ
    have hNM : Mh ≤ max N Mh := le_max_right N Mh
    linarith
  · -- `τ.re - logSlack ≤ w.re`
    have h1 := hre_ge w hwρ
    have h2 : ρ ≤ X + c₁ * (Real.log (1 + ‖τ‖) + Real.pi) := le_of_lt hρ_lt_logSlack
    have h3 : X + c₁ * (Real.log (1 + ‖τ‖) + Real.pi) = logSlack c₁ X τ := by
      rw [logSlack_apply]
    linarith
  · -- `|τ.im| - logSlack ≤ |w.im|`
    have h1 : |τ.im - w.im| ≤ ρ := by
      have h := Complex.abs_im_le_norm (τ - w)
      have h2 : (τ - w).im = τ.im - w.im := by simp
      rw [h2] at h
      have h3 : ‖τ - w‖ = dist w τ := by rw [dist_eq_norm, norm_sub_rev]
      rw [h3] at h
      linarith [hwρ]
    have h2 : ρ ≤ X + c₁ * (Real.log (1 + ‖τ‖) + Real.pi) := le_of_lt hρ_lt_logSlack
    have h3 : X + c₁ * (Real.log (1 + ‖τ‖) + Real.pi) = logSlack c₁ X τ := by
      rw [logSlack_apply]
    have h4 : |τ.im| - |w.im| ≤ |τ.im - w.im| := abs_sub_abs_le_abs_sub _ _
    linarith

end

end Work.SatFree

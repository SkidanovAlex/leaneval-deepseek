import Mathlib
import Submission.Work.MRMT.Weyl.integral_ball_eq_mul_of_differentiable
import Submission.Work.MRMT.Found.analytic_eq_zero_of_memLp_two

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Weyl

open MeasureTheory Metric Complex Filter
open scoped Topology

/-- **An entire function which agrees a.e. with a `C/‖z‖`-decaying function vanishes.**

Let `u` be entire, `g` locally integrable with `u =ᵐ g`, and suppose `‖g z‖ ≤ C / ‖z‖`
for all `‖z‖ ≥ R`. Then `u = 0`.

The proof: the mean value property for `u` over balls, combined with the *pointwise*
bound on `g` and the a.e. equality `u =ᵐ g`, upgrades the a.e. decay of `u` to the
pointwise bound `‖u c‖ ≤ 2C / ‖c‖` for `‖c‖ > 2 max(R,0)`.  Hence `u → 0` along
`cocompact`, and Liouville's theorem (`Differentiable.apply_eq_of_tendsto_cocompact`)
forces `u = 0`. -/
theorem analyticOn_eq_zero_of_ae_eq_of_decay {u g : ℂ → ℂ}
    (hu : AnalyticOn ℂ u Set.univ)
    (hg : MeasureTheory.LocallyIntegrable g (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (heq : u =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℂ)] g)
    (hdec : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖g z‖ ≤ C / ‖z‖) :
    u = 0 := by
  obtain ⟨C, R, hdec⟩ := hdec
  have hdiff : Differentiable ℂ u := differentiableOn_univ.mp hu.differentiableOn
  -- the constant `C` is nonnegative (a direct consequence of the decay of `g`)
  have hC0 : 0 ≤ C := by
    have hge : R ≤ ‖(((max R 1 + 1 : ℝ) : ℂ))‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith [le_max_left R 1]
    have h1 := hdec _ hge
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
    have h2 : 0 ≤ C / (max R 1 + 1) := le_trans (norm_nonneg _) h1
    have hden : (0:ℝ) < max R 1 + 1 := by linarith [le_max_right R 1]
    have h3 : 0 ≤ C / (max R 1 + 1) * (max R 1 + 1) := mul_nonneg h2 hden.le
    rwa [div_mul_cancel₀ C hden.ne'] at h3
  let R' : ℝ := max R 0
  have hR'0 : 0 ≤ R' := le_max_right R 0
  -- pointwise bound obtained from the a.e. equality and the ball mean value property
  have hbound : ∀ c : ℂ, 2 * R' < ‖c‖ → ‖u c‖ ≤ 2 * C / ‖c‖ := by
    intro c hc
    have hcnormpos : 0 < ‖c‖ := by linarith [hR'0, hc]
    have hgbound : ∀ w ∈ Metric.ball c (‖c‖/2), ‖g w‖ ≤ 2 * C / ‖c‖ := by
      intro w hw
      have hdist : ‖w - c‖ < ‖c‖/2 := by
        rw [Metric.mem_ball, dist_eq_norm] at hw; exact hw
      have hwnorm : ‖c‖/2 < ‖w‖ := by
        have htri : ‖c‖ ≤ ‖w‖ + ‖w - c‖ := by
          have := norm_sub_le w (w - c)
          rwa [sub_sub_cancel] at this
        linarith
      have hwR : R ≤ ‖w‖ := by
        have hRR : R' < ‖c‖/2 := by linarith
        have hR'R : R ≤ R' := le_max_left _ _
        linarith
      have h1 : ‖g w‖ ≤ C / ‖w‖ := hdec w hwR
      have h2 : C / ‖w‖ ≤ 2 * C / ‖c‖ := by
        have h3 : C / ‖w‖ ≤ C / (‖c‖ / 2) :=
          div_le_div_of_nonneg_left hC0 (by positivity) (by linarith)
        have h4 : C / (‖c‖ / 2) = 2 * C / ‖c‖ := by
          rw [div_div_eq_mul_div]; ring
        linarith
      linarith
    have hMV : ∫ z in Metric.ball c (‖c‖/2), u z = ((Real.pi * (‖c‖/2) ^ 2 : ℝ) : ℂ) * u c :=
      integral_ball_eq_mul_of_differentiable hdiff (c := c) (R := ‖c‖/2) (by positivity)
    have hinteq : ∫ z in Metric.ball c (‖c‖/2), u z = ∫ z in Metric.ball c (‖c‖/2), g z := by
      refine MeasureTheory.setIntegral_congr_ae measurableSet_ball ?_
      filter_upwards [heq] with z hz
      intro _
      exact hz
    have hvolfin : (volume : Measure ℂ) (Metric.ball c (‖c‖/2)) < ⊤ := by
      rw [Complex.volume_ball]
      exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) ENNReal.coe_lt_top
    have hIntbound : ‖∫ z in Metric.ball c (‖c‖/2), g z‖
        ≤ (2 * C / ‖c‖) * ((‖c‖/2) ^ 2 * Real.pi) := by
      have := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℂ))
        (f := g) (s := Metric.ball c (‖c‖/2)) (C := 2 * C / ‖c‖) hvolfin hgbound
      rw [MeasureTheory.Measure.real_def] at this
      rwa [Work.MRMT.Found.real_volume_ball c (by positivity)] at this
    have hkey : (Real.pi * (‖c‖/2) ^ 2) * ‖u c‖
        ≤ (2 * C / ‖c‖) * ((‖c‖/2) ^ 2 * Real.pi) := by
      have hnorm : (Real.pi * (‖c‖/2) ^ 2) * ‖u c‖
          = ‖∫ z in Metric.ball c (‖c‖/2), u z‖ := by
        rw [hMV, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [hnorm, hinteq]; exact hIntbound
    have hpi : 0 < Real.pi * (‖c‖/2) ^ 2 := by positivity
    have hcomm : (2 * C / ‖c‖) * ((‖c‖/2) ^ 2 * Real.pi)
        = (Real.pi * (‖c‖/2) ^ 2) * (2 * C / ‖c‖) := by ring
    rw [hcomm] at hkey
    exact le_of_mul_le_mul_left hkey hpi
  -- `u` tends to `0` at infinity
  have htend : Tendsto u (cocompact ℂ) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [Filter.hasBasis_cocompact.eventually_iff]
    refine ⟨Metric.closedBall 0 (max (2 * R') (2 * C / ε) + 1), isCompact_closedBall _ _, ?_⟩
    intro z hz
    have hz_gt : max (2 * R') (2 * C / ε) + 1 < ‖z‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz
    have hzpos : 0 < ‖z‖ := by
      have h2Cε : 0 ≤ 2 * C / ε := div_nonneg (by linarith) hε.le
      linarith [le_max_right (2 * R') (2 * C / ε)]
    rw [dist_zero_right]
    calc ‖u z‖ ≤ 2 * C / ‖z‖ := hbound z (by linarith [le_max_left (2 * R') (2 * C / ε)])
      _ < ε := by
          rw [div_lt_iff₀ hzpos]
          have hlt : 2 * C / ε < ‖z‖ := by
            linarith [le_max_right (2 * R') (2 * C / ε)]
          have := (div_lt_iff₀ hε).mp hlt
          linarith
  exact funext fun z => hdiff.apply_eq_of_tendsto_cocompact z htend

end Work.MRMT.Weyl
